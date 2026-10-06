/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupCutoffTime
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction

public section

open Set CKN CKN.Foundation.Parabolic
noncomputable section
namespace ESS

/-- The spatial cutoff times the past time cutoff used in the rescaled local
energy inequality. -/
@[expose] def blowupEnergyCutoff (R a b : ℝ) (z : Vec3 × ℝ) : ℝ :=
  canonicalBallCutoff (0 : Vec3) R (R + 1) z.1 *
    blowupTimeCutoff a b z.2

/-- The energy cutoff is an admissible nonnegative test on a fixed larger
past cylinder. -/
theorem blowupEnergyCutoff_test
    (R a b : ℝ) (hR : 0 < R) (hb : b < 0) :
    blowupEnergyCutoff R a b ∈
      spaceTimeTestFunction (V := ℝ)
        (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) ∧
      ∀ z, 0 ≤ blowupEnergyCutoff R a b z := by
  let ζ : Vec3 → ℝ := canonicalBallCutoff 0 R (R + 1)
  let η : ℝ → ℝ := blowupTimeCutoff a b
  have hr : 0 ≤ R := hR.le
  have hR' : R < R + 1 := by linarith only []
  have hζs : ContDiff ℝ (⊤ : ℕ∞) ζ :=
    canonicalBallCutoff_smooth 0 hr hR'
  have hηs : ContDiff ℝ (⊤ : ℕ∞) η :=
    blowupTimeCutoff_smooth a b
  have hζc : HasCompactSupport ζ :=
    canonicalBallCutoff_hasCompactSupport hr hR'
  have hηc : HasCompactSupport η :=
    blowupTimeCutoff_hasCompactSupport a b hb
  have hψs : ContDiff ℝ (⊤ : ℕ∞) (blowupEnergyCutoff R a b) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ζ z.1 * η z.2)
    exact (hζs.comp contDiff_fst).mul (hηs.comp contDiff_snd)
  let K : Set (Vec3 × ℝ) := tsupport ζ ×ˢ tsupport η
  have hK : IsCompact K := hζc.isCompact.prod hηc.isCompact
  have hsupp : Function.support (blowupEnergyCutoff R a b) ⊆ K := by
    intro z hz
    change ζ z.1 * η z.2 ≠ 0 at hz
    exact ⟨subset_tsupport ζ (mul_ne_zero_iff.mp hz).1,
      subset_tsupport η (mul_ne_zero_iff.mp hz).2⟩
  have hψc : HasCompactSupport (blowupEnergyCutoff R a b) := by
    apply HasCompactSupport.intro hK
    intro z hz
    by_contra hne
    exact hz (hsupp hne)
  have hts : tsupport (blowupEnergyCutoff R a b) ⊆ K :=
    closure_minimal hsupp (hζc.isCompact.isClosed.prod hηc.isCompact.isClosed)
  have hψsupp : tsupport (blowupEnergyCutoff R a b) ⊆
      CKN.euclideanBall 0 (R + 1) ×ˢ Ioo (a - 2) 0 := by
    intro z hz
    have hzK := hts hz
    exact ⟨canonicalBallCutoff_tsupport_subset_outer hr hR' hzK.1,
      blowupTimeCutoff_tsupport_subset_open a b hb hzK.2⟩
  refine ⟨⟨hψs, hψc, hψsupp⟩, ?_⟩
  intro z
  change 0 ≤ ζ z.1 * η z.2
  exact mul_nonneg (canonicalBallCutoff_nonneg 0 R (R + 1) z.1)
    (blowupTimeCutoff_bounds a b z.2).1

/-- The energy cutoff equals one on the target spatial ball and past time
plateau. -/
theorem blowupEnergyCutoff_eq_one
    {R a b : ℝ} (hR : 0 < R) (hb : b < 0)
    {z : Vec3 × ℝ}
    (hz : z.1 ∈ CKN.euclideanBall 0 R ∧ z.2 ∈ Icc a b) :
    blowupEnergyCutoff R a b z = 1 := by
  have hr : 0 ≤ R := hR.le
  have hR' : R < R + 1 := by linarith only []
  simp only [blowupEnergyCutoff,
    canonicalBallCutoff_eq_one_on_inner hr hR' hz.1,
    blowupTimeCutoff_eq_one hb hz.2.1 hz.2.2, one_mul]

end ESS
