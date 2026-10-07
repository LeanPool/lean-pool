/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyWeak

/-!
# The source of the mollified velocity

The kernel of the point-tested momentum identity is written with the strongly
measurable modification of the force, which changes the source only on a null
set of times. The resulting source is jointly measurable, and on almost every
time slice it is a sum of convolutions of square-integrable fields with the
mollifier and its derivatives, bounded uniformly in space by an integrable
function of time. These are the ingredients of the local energy inequality
`eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Convolution

noncomputable section

namespace CKN.Leray

section Source

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

/-- The transport-minus-viscous tensor of the forced regularized solution. -/
@[expose]
def leTensor (j k : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z j *
    forcedRegRep ρ ε hε ha hf z k - forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) z k j

/-- The pressure of the forced regularized solution as a space-time field. -/
@[expose]
def lePressure (z : Vec3 × ℝ) : ℝ :=
  forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) z + forcePressure f hf z

/-- The kernel of the point-tested momentum identity with the modified force. -/
@[expose]
def leKernelF (η : Vec3 → ℝ) (x : Vec3) (k : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  ∑ j : Fin 3, leTensor ρ ε hε ha hf j k z * CKN.spatialDeriv η j (x - z.1) +
    lePressure ρ ε hε ha hf z * CKN.spatialDeriv η k (x - z.1) -
    forcedForceMod f hf z k * η (x - z.1)

/-- The source of the mollified velocity with the modified force. -/
@[expose]
def leSF (η : Vec3 → ℝ) (x : Vec3) (t : ℝ) (k : Fin 3) : ℝ :=
  ∫ y, leKernelF ρ ε hε ha hf η x k (y, t)

theorem ae_leS_eq_leSF (η : Vec3 → ℝ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)), ∀ x k,
      leS ρ ε hε ha hf η x t k = leSF ρ ε hε ha hf η x t k := by
  filter_upwards [ae_forcedForceMod_slice hf hT] with t ht x k
  unfold leS leSF
  refine integral_congr_ae ?_
  filter_upwards [ht.2] with y hy
  simp only [leKernel, leKernelF, leTensor, lePressure]
  rw [hy]

/-- The weak time derivative of the mollified velocity with the modified
source. -/
theorem hasWeakDerivOn_leW_F {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (x : Vec3) (k : Fin 3) {T : ℝ} (hT : 0 < T) :
    CKN.HasWeakDerivOn (Ioo 0 T) (fun t => leW ρ ε hε ha hf η x t k)
      (fun t => -leSF ρ ε hε ha hf η x t k) := by
  intro θ hθ
  rw [hasWeakDerivOn_leW ρ ε hε ha hf hη hηc x k hT θ hθ]
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 (ae_leS_eq_leSF ρ ε hε ha hf η hT)]
    with t ht hts
  rw [ht hts x k]

end Source

end CKN.Leray

end
