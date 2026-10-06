/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureSlice
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureUniqueness

/-!
# Linearity of the force pressure

The field (I - ℙ) f of `lem:force-pressure` is the orthogonal projection of
f onto the closure of the test gradients: it lies in that closure, and the
Leray part ℙ f is orthogonal to every test gradient. Hence it is linear in
f, and by uniqueness the L⁶ pressure of one slice is linear up to null
sets.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The real pairing of two spatial L² fields is the integral of the dot
product of their coordinate representatives. -/
theorem inner_eq_integral_realVectorL2Representative (u w : RealVectorL2) :
    inner ℝ u w = ∫ x : Vec3, ∑ i : Fin 3,
      realVectorL2Representative u x i * realVectorL2Representative w x i := by
  rw [L2.inner_def]
  rw [← vec3ToL2Vec3_measurePreserving.integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
  congr 1
  funext x
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [realVectorL2Representative_apply, mul_comm]

/-- The Leray part of a field is orthogonal to every test gradient. -/
theorem realLerayProjection_mem_orthogonal_testGradientSpan (v : RealVectorL2) :
    realLerayProjection v ∈ forcePressureTestGradientSpanᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    rw [inner_forcePressureTestGradientL2_eq_integral]
    exact (realLerayProjection_isWeakDivFree v).2 φ
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [real_inner_smul_left, hx, mul_zero]

/-- The field (I - ℙ) f of `lem:force-pressure` is the orthogonal projection
of f onto the closure of the test gradients. -/
theorem forcePressureGradientL2_eq_starProjection (v : RealVectorL2) :
    forcePressureGradientL2 v =
      forcePressureTestGradientSpan.topologicalClosure.starProjection v := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (forcePressureGradientL2_mem_topologicalClosure v)
  intro w hw
  have hsub : v - forcePressureGradientL2 v = realLerayProjection v := by
    rw [forcePressureGradientL2]
    abel
  rw [hsub]
  rw [← Submodule.orthogonal_orthogonal_eq_closure] at hw
  exact Submodule.inner_right_of_mem_orthogonal
    (realLerayProjection_mem_orthogonal_testGradientSpan v) hw

/-- The field (I - ℙ) f is additive in f. -/
theorem forcePressureGradientL2_add (v w : RealVectorL2) :
    forcePressureGradientL2 (v + w) =
      forcePressureGradientL2 v + forcePressureGradientL2 w := by
  simp only [forcePressureGradientL2_eq_starProjection, map_add]

/-- The field (I - ℙ) f is homogeneous in f. -/
theorem forcePressureGradientL2_smul (c : ℝ) (v : RealVectorL2) :
    forcePressureGradientL2 (c • v) = c • forcePressureGradientL2 v := by
  simp only [forcePressureGradientL2_eq_starProjection, map_smul]

/-- The force pressure of `lem:force-pressure` on one time slice: an L⁶
function whose weak gradient is the field (I - ℙ) f. -/
@[expose]
def forcePressureSlice (v : RealVectorL2) : Vec3 → ℝ :=
  Classical.choose (exists_forcePressureSlice v)

/-- The slice force pressure lies in L⁶. -/
theorem forcePressureSlice_memLp (v : RealVectorL2) :
    MemLp (forcePressureSlice v) 6 volume :=
  (Classical.choose_spec (exists_forcePressureSlice v)).1

/-- The homogeneous Sobolev bound for the slice force pressure. -/
theorem forcePressureSlice_eLpNorm_le (v : RealVectorL2) :
    eLpNorm (forcePressureSlice v) 6 volume ≤
      gagliardoNirenbergSobolevConstant * eLpNorm (forcePressureGradientL2 v) 2 volume :=
  (Classical.choose_spec (exists_forcePressureSlice v)).2.1

/-- The weak gradient of the slice force pressure is (I - ℙ) f. -/
theorem forcePressureSlice_hasWeakGradientOn (v : RealVectorL2) :
    HasWeakGradientOn (Set.univ : Set Vec3) (forcePressureSlice v)
      (realVectorL2Representative (forcePressureGradientL2 v)) :=
  (Classical.choose_spec (exists_forcePressureSlice v)).2.2

/-- A weak gradient is unchanged when the function is modified on a null
set. -/
theorem hasWeakGradientOn_congr_ae_left {p q : Vec3 → ℝ} {G : Vec3 → Vec3}
    (hpq : p =ᵐ[volume] q) (h : HasWeakGradientOn (Set.univ : Set Vec3) p G) :
    HasWeakGradientOn (Set.univ : Set Vec3) q G := by
  intro i φ hφ hφc hφU
  rw [← h i φ hφ hφc hφU]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hpq] with x hx
  rw [hx]

/-- A weak gradient may be modified on a null set. -/
theorem hasWeakGradientOn_congr_ae_right {p : Vec3 → ℝ} {G H : Vec3 → Vec3}
    (hGH : G =ᵐ[volume] H) (h : HasWeakGradientOn (Set.univ : Set Vec3) p G) :
    HasWeakGradientOn (Set.univ : Set Vec3) p H := by
  intro i φ hφ hφc hφU
  rw [h i φ hφ hφc hφU]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hGH] with x hx
  rw [hx]

private theorem forcePressure_hasWeakGradientOn_combination {p₁ p₂ : Vec3 → ℝ}
    {G₁ G₂ : Vec3 → Vec3} (a b : ℝ)
    (hp₁ : MemLp p₁ 6 volume) (hp₂ : MemLp p₂ 6 volume)
    (hG₁ : MemLp G₁ 2 volume) (hG₂ : MemLp G₂ 2 volume)
    (h₁ : HasWeakGradientOn (Set.univ : Set Vec3) p₁ G₁)
    (h₂ : HasWeakGradientOn (Set.univ : Set Vec3) p₂ G₂) :
    HasWeakGradientOn (Set.univ : Set Vec3) (fun x => a * p₁ x + b * p₂ x)
      (fun x => a • G₁ x + b • G₂ x) := by
  intro i
  rw [hasWeakPartialDerivOn_iff_forall_testFunction]
  intro ψ
  have e₁ := (hasWeakPartialDerivOn_iff_forall_testFunction.1 (h₁ i)) ψ
  have e₂ := (hasWeakPartialDerivOn_iff_forall_testFunction.1 (h₂ i)) ψ
  simp only [setIntegral_univ] at e₁ e₂ ⊢
  have hψc : Continuous ψ.toFun := ψ.contDiff.continuous
  have hψd : Continuous fun x => ψ.partialDeriv i x :=
    (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψdc : HasCompactSupport fun x => ψ.partialDeriv i x :=
    ψ.hasCompactSupport.fderiv (𝕜 := ℝ) |>.comp_left
      (g := fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) (by simp)
  have hi₁ : Integrable (fun x => p₁ x * ψ.partialDeriv i x) volume :=
    (hp₁.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hψd hψdc
  have hi₂ : Integrable (fun x => p₂ x * ψ.partialDeriv i x) volume :=
    (hp₂.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hψd hψdc
  have hG₁local := (memLp_pi_iff.mp hG₁ i).locallyIntegrable (by norm_num)
  have hj₁ : Integrable (fun x => G₁ x i * ψ x) volume :=
    hG₁local.integrable_smul_right_of_hasCompactSupport hψc ψ.hasCompactSupport
  have hG₂local := (memLp_pi_iff.mp hG₂ i).locallyIntegrable (by norm_num)
  have hj₂ : Integrable (fun x => G₂ x i * ψ x) volume :=
    hG₂local.integrable_smul_right_of_hasCompactSupport hψc ψ.hasCompactSupport
  have hleft : (fun x => (a * p₁ x + b * p₂ x) * ψ.partialDeriv i x) =
      fun x => a * (p₁ x * ψ.partialDeriv i x) + b * (p₂ x * ψ.partialDeriv i x) := by
    funext x
    ring
  have hright : (fun x => (a • G₁ x + b • G₂ x) i * ψ x) =
      fun x => a * (G₁ x i * ψ x) + b * (G₂ x i * ψ x) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hleft, hright, integral_add (hi₁.const_mul a) (hi₂.const_mul b),
    integral_add (hj₁.const_mul a) (hj₂.const_mul b), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, e₁, e₂]
  ring

/-- The slice force pressure is linear up to null sets. -/
theorem forcePressureSlice_linearCombination_ae (a b : ℝ) (v w : RealVectorL2) :
    forcePressureSlice (a • v + b • w) =ᵐ[volume]
      fun x => a * forcePressureSlice v x + b * forcePressureSlice w x := by
  have hGv := realVectorL2Representative_memLp_two (forcePressureGradientL2 v)
  have hGw := realVectorL2Representative_memLp_two (forcePressureGradientL2 w)
  have hcomb := forcePressure_hasWeakGradientOn_combination a b
    (forcePressureSlice_memLp v) (forcePressureSlice_memLp w) hGv hGw
    (forcePressureSlice_hasWeakGradientOn v) (forcePressureSlice_hasWeakGradientOn w)
  have hrep := realVectorL2Representative_linearCombination_ae a b
    (forcePressureGradientL2 v) (forcePressureGradientL2 w)
  have hgrad : HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => a * forcePressureSlice v x + b * forcePressureSlice w x)
      (realVectorL2Representative (forcePressureGradientL2 (a • v + b • w))) := by
    apply hasWeakGradientOn_congr_ae_right _ hcomb
    filter_upwards [hrep] with x hx
    rw [forcePressureGradientL2_add, forcePressureGradientL2_smul,
      forcePressureGradientL2_smul, hx]
    rfl
  have hmem : MemLp (fun x => a * forcePressureSlice v x + b * forcePressureSlice w x)
      6 volume :=
    ((forcePressureSlice_memLp v).const_mul a).add ((forcePressureSlice_memLp w).const_mul b)
  exact ae_eq_of_memLp_six_of_hasWeakGradientOn (forcePressureSlice_memLp _) hmem
    (forcePressureSlice_hasWeakGradientOn _) hgrad

end CKN.Leray
