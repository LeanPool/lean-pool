/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ThetaPshConvexCombination
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ThetaPshComparison

/-!
# The Perron barrier family of Xia's domination principle

In the ordered case `phi ≤ psi` of Xia's Theorem 2.4.5 the barriers are the
Perron envelopes

  `eta a := P_theta (a * phi + (1 - a) * psi)`,  `a > 1`,

which in this workspace is `rooftopEnvelope theta (convexComb a phi psi)`
(`xia-sgpt:page-0088`; `convexComb a` is Xia's obstacle exactly, with the
weight `a > 1` outside `[0,1]`).  Two of the four properties the closing stage
`Pending.DominationPrincipleReduction.le_of_null_barrier_family` asks of the
family are unconditional facts about that envelope and are proved here:

* the family is **antitone in `a`** (the obstacle is, because `phi ≤ psi` and
  increasing `a` moves the obstacle towards `phi` with a negative weight on
  `psi`);
* every member **lies below `phi`**, since the obstacle at `a = 1` is `phi`
  itself and the rooftop envelope of a genuine potential is that potential.

The remaining two — that each member is a genuine `theta`-PSH potential of the
reference mass (Xia's Lemma 2.4.4 and Corollary 2.4.3), and that each meets
`phi` off a `theta^n_phi`-null set (the measure chain built from Theorem 2.4.4
and Lemma 2.4.2) — are the analytic middle stage and are not addressed here.
-/

@[expose] public section

open Set

namespace SGPT.Foundations.Analysis.Pending.DominationPrincipleBarrier

open FirstPass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The convex combination at weight one is the first potential; no finiteness
is needed, because `EReal` multiplication by the real `0` is `0`. -/
theorem convexComb_one (u v : M → EReal) : convexComb (1 : ℝ) u v = u := by
  funext x
  rw [convexComb_apply]
  norm_num

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- **The Perron obstacle of Theorem 2.4.5 is antitone in `a`.**  Below the
pole set of `phi` both sides are `-∞`; elsewhere both are finite and the
inequality is `(b - a)(phi - psi) ≤ 0`. -/
theorem convexComb_antitone_of_le {phi psi : M → EReal} (hle : phi ≤ psi)
    (hpsitop : ∀ x, psi x ≠ ⊤) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    convexComb b phi psi ≤ convexComb a phi psi := by
  intro x
  rw [convexComb_apply, convexComb_apply]
  by_cases hbot : phi x = ⊥
  · rw [hbot, EReal.coe_mul_bot_of_pos (lt_of_lt_of_le ha hab), EReal.bot_add]
    exact bot_le
  · have hptop : phi x ≠ ⊤ := by
      intro h
      exact hpsitop x (top_le_iff.mp (h ▸ hle x))
    have hlex : phi x ≤ psi x := hle x
    lift phi x to ℝ using ⟨hptop, hbot⟩ with p hp
    have hqbot : psi x ≠ ⊥ := ((EReal.bot_lt_coe p).trans_le hlex).ne'
    lift psi x to ℝ using ⟨hpsitop x, hqbot⟩ with q hq
    have hpq : p ≤ q := EReal.coe_le_coe_iff.mp hlex
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul,
      ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith

/-- The rooftop envelope of a genuine `theta`-PSH potential is that potential:
every competitor lies below it quasi-everywhere, hence everywhere. -/
theorem rooftopEnvelope_eq_self {theta : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential theta u) : rooftopEnvelope theta u = u := by
  refine le_antisymm ?_ (self_le_rooftopEnvelope hu)
  refine (rooftopEnvelope_le_iff
    (ManifoldQuasiPlurisubharmonic.upperSemicontinuous hu.1.quasiPlurisubharmonic)).2 ?_
  intro w hw hwu
  exact hw.1.le_of_quasiEverywhere_le hu.1 hwu

/-- **The barrier family is antitone**, which is the `hanti` hypothesis of
`Pending.DominationPrincipleReduction.le_of_null_barrier_family`. -/
theorem rooftopEnvelope_convexComb_antitone {theta : SmoothRealForm n M 2}
    {phi psi : M → EReal} (hle : phi ≤ psi) (hpsitop : ∀ x, psi x ≠ ⊤)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    rooftopEnvelope theta (convexComb b phi psi) ≤
      rooftopEnvelope theta (convexComb a phi psi) :=
  rooftopEnvelope_mono (convexComb_antitone_of_le hle hpsitop ha hab)

/-- **Every barrier lies below the reference**, which is the `hle` hypothesis
of `Pending.DominationPrincipleReduction.le_of_null_barrier_family`.  This is
Xia's `eta_a ≤ P_theta (a phi + (1 - a) phi) = phi` on `xia-sgpt:page-0088`. -/
theorem rooftopEnvelope_convexComb_le {theta : SmoothRealForm n M 2}
    {phi psi : M → EReal} (hphi : IsThetaPshPotential theta phi)
    (hle : phi ≤ psi) (hpsitop : ∀ x, psi x ≠ ⊤) {a : ℝ} (ha : 1 ≤ a) :
    rooftopEnvelope theta (convexComb a phi psi) ≤ phi := by
  have h := rooftopEnvelope_convexComb_antitone (theta := theta) hle hpsitop
    (a := 1) (b := a) one_pos ha
  rwa [convexComb_one, rooftopEnvelope_eq_self hphi] at h

/-- The `θ`-PSH hypothesis in the convenient form: a genuine potential never
takes the value `⊤`. -/
theorem ne_top_of_isThetaPshPotential {theta : SmoothRealForm n M 2}
    {u : M → EReal} (hu : IsThetaPshPotential theta u) (x : M) : u x ≠ ⊤ :=
  hu.1.quasiPlurisubharmonic.ne_top x

end

end SGPT.Foundations.Analysis.Pending.DominationPrincipleBarrier
