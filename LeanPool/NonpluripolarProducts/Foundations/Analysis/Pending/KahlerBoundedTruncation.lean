/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerDomination
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BoundedGlobalTruncation

/-!
# Truncated global mixed measures on a compact Kähler manifold

`Pending.BoundedGlobalTruncation` produces the BEGZ measure `ν_l` of a truncated
tuple, but only in a *semipositive* background. On a compact Kähler manifold that
hypothesis is never a restriction: `Pending.KahlerDomination` supplies one
constant `A > 0` making every `θ i + A ω` semipositive, and a `θ`-PSH function is
`(θ + η)`-PSH for any semipositive `η`. So the potentials are unchanged and only
the backgrounds move, inside their own cohomology direction.

The result is unconditional: for *any* raw `θ`-PSH tuple on a compact Kähler
manifold and any truncation levels, the truncated tuple has a global mixed
non-pluripolar measure of finite total mass against the enlarged backgrounds.

Independence of that mass from the truncation level is the separate
integration-by-parts statement and is not asserted here.
-/

@[expose] public section

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.KahlerDomination

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
open GlobalNonPluripolar BoundedGlobalProduct

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

variable [CompactSpace M]

/-- **A common semipositive enlargement of a finite family of backgrounds, for
which the given potentials are still `θ`-PSH.** The potentials are literally
unchanged; only the backgrounds move, by a nonnegative multiple of `ω`. -/
theorem exists_pos_semipositive_thetaPlurisubharmonic (omega : KahlerBackground n M)
    (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i)) :
    ∃ A : ℝ, 0 < A ∧ (∀ i, (θ i + A • omega.form).val.IsSemipositive) ∧
      ∀ i, ThetaPlurisubharmonic (θ i + A • omega.form).val (u i) := by
  obtain ⟨A, hA, hsemi⟩ := exists_pos_forall_isSemipositive_add_smul omega θ
  refine ⟨A, hA, hsemi, fun i => ?_⟩
  exact LocalPotentials.thetaPlurisubharmonic_add_of_semipositive (hu i)
    (isSemipositive_smul (KahlerBackground.isSemipositive omega) hA.le)

omit [CompactSpace M] in
/-- **Bounded global truncations in a positive background**
(`gnpp:bounded-global-truncation`), for a constant supplied in advance. A raw
`θ`-PSH function is raw `η`-PSH for `η = θ + A ω`, so its truncations are raw
`η`-PSH; on a nonempty compact manifold they are moreover globally bounded. -/
theorem thetaPlurisubharmonic_max_const_of_dominating (omega : KahlerBackground n M)
    {A : ℝ} (hA : 0 ≤ A) {a : ClosedRealOneOneForm n M}
    (ha : (a + A • omega.form).val.IsSemipositive) {v : M → EReal}
    (hv : ThetaPlurisubharmonic a.val v) (c : ℝ) :
    ThetaPlurisubharmonic (a + A • omega.form).val
      (fun x => Max.max (v x) ((c : ℝ) : EReal)) :=
  thetaPlurisubharmonic_max_const ha
    (LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hv
      (isSemipositive_smul (KahlerBackground.isSemipositive omega) hA)) c

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- **The BEGZ measure `ν_l` exists with finite mass on any compact Kähler
manifold**, with no positivity assumption on the backgrounds themselves. -/
theorem exists_globalMixedMeasure_truncation_isFiniteMeasure
    (omega : KahlerBackground n M) (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (c : Fin n → ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∃ (hsemi : ∀ i, (θ i + A • omega.form).val.IsSemipositive)
      (hu' : ∀ i, ThetaPlurisubharmonic (θ i + A • omega.form).val (u i)),
      IsFiniteMeasure (globalMixedMeasure (fun i => θ i + A • omega.form)
        (fun i x => Max.max (u i x) ((c i : ℝ) : EReal))
        (thetaPlurisubharmonic_truncation hsemi hu' c)) := by
  obtain ⟨A, hA, hsemi, hu'⟩ := exists_pos_semipositive_thetaPlurisubharmonic omega hu
  exact ⟨A, hA, hsemi, hu',
    globalMixedMeasure_truncation_isFiniteMeasure hsemi hu' c⟩

end

end SGPT.Foundations.Analysis.Pending.KahlerDomination
