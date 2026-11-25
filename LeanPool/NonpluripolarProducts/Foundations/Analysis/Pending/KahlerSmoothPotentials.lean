/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothDDCForm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalPotentials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerDomination

/-! # Smooth potentials dominated by a compact Kähler background -/

@[expose] public section

noncomputable section

open Set
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SmoothDDCForm

open FirstPass FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable [CompactSpace M]

/-- **Every chart-smooth function is quasi-plurisubharmonic.** On a compact
Kähler manifold a smooth function is `(θ + Cω)`-PSH for a large enough `C`,
uniformly over a finite family of backgrounds and functions. This is Kähler
domination applied to the backgrounds and to the `ddᶜ` of the functions. -/
theorem exists_pos_thetaPlurisubharmonic_smooth {ι : Type*} [Finite ι]
    (omega : KahlerBackground n M) (θ : ι → ClosedRealOneOneForm n M)
    (ψ : ι → M → ℝ) (hψ : ∀ i, ChartSmooth (n := n) (ψ i)) :
    ∃ C : ℝ, 0 < C ∧ (∀ i, (θ i + C • omega.form).val.IsSemipositive) ∧
      ∀ i, ThetaPlurisubharmonic (θ i + C • omega.form).val
        fun x => ((ψ i x : ℝ) : EReal) := by
  classical
  let := Fintype.ofFinite ι
  have hherm : omega.form.val.IsHermitian := omega.isKahler.1
  -- a constant dominating every background
  obtain ⟨A, hA, hAdom⟩ :=
    KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega θ
  -- a constant dominating every `ddᶜψ i`
  have hlocal : ∀ i : ι, ∃ B : ℝ, 0 < B ∧ ∀ (e : ComplexChart n M) (z : ComplexModel n),
      z ∈ e.val.target → ∀ v : ComplexModel n,
        0 ≤ (ddcForm (ψ i) (hψ i)).coeff e z ![v, Complex.I • v] +
          B * omega.form.val.coeff e z ![v, Complex.I • v] := fun i =>
    KahlerDomination.exists_isSemipositive_add_smul _ _ hherm
  choose B hB hBdom using hlocal
  set C : ℝ := A + ∑ i, B i with hCdef
  have hBsum : (0 : ℝ) ≤ ∑ i, B i := Finset.sum_nonneg fun j _ => (hB j).le
  have hCpos : 0 < C := by rw [hCdef]; linarith
  -- the pointwise inequalities, in raw coefficient form
  have hω : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n, 0 ≤ omega.form.val.coeff e z ![v, Complex.I • v] :=
    fun e z hz v => omega.isSemipositive e z hz v
  have hAi : ∀ (i : ι) (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n, 0 ≤ (θ i).val.coeff e z ![v, Complex.I • v] +
        A * omega.form.val.coeff e z ![v, Complex.I • v] := by
    intro i e z hz v
    simpa [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]
      using hAdom i e z hz v
  have hgrow : ∀ (i : ι) (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      ∀ v : ComplexModel n, (A + B i) * omega.form.val.coeff e z ![v, Complex.I • v] ≤
        C * omega.form.val.coeff e z ![v, Complex.I • v] := by
    intro i e z hz v
    refine mul_le_mul_of_nonneg_right ?_ (hω e z hz v)
    have := Finset.single_le_sum (f := B) (fun j _ => (hB j).le) (Finset.mem_univ i)
    rw [hCdef]; linarith
  have hsemi : ∀ i, (θ i + C • omega.form).val.IsSemipositive := by
    intro i e z hz v
    have h1 := hAi i e z hz v
    have h2 : A * omega.form.val.coeff e z ![v, Complex.I • v] ≤
        C * omega.form.val.coeff e z ![v, Complex.I • v] := by
      refine mul_le_mul_of_nonneg_right ?_ (hω e z hz v)
      rw [hCdef]; linarith
    have : 0 ≤ (θ i).val.coeff e z ![v, Complex.I • v] +
        C * omega.form.val.coeff e z ![v, Complex.I • v] := by linarith
    simpa [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul] using this
  refine ⟨C, hCpos, hsemi, fun i => ?_⟩
  rw [LocalPotentials.thetaPlurisubharmonic_smooth_iff _ _ (hψ i)]
  intro e z hz v
  have h1 := hAi i e z hz v
  have h2 := hBdom i e z hz v
  have h3 := hgrow i e z hz v
  simp only [ddcForm_coeff] at h2
  have hfinal : 0 ≤ (θ i).val.coeff e z ![v, Complex.I • v] +
      C * omega.form.val.coeff e z ![v, Complex.I • v] +
      smoothDDC (fun y => ψ i (e.val.symm y)) z ![v, Complex.I • v] := by
    nlinarith [h1, h2, h3]
  simpa [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul] using hfinal

end SGPT.Foundations.Analysis.Pending.SmoothDDCForm
