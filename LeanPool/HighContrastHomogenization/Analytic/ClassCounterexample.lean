/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.ClassHonesty

/-!
# High-contrast homogenization: Analytic.ClassCounterexample

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The domain hypothesis on `H¹_a(V)`, and smoothness on `V`

Two facts about the coefficient Sobolev space `H¹_a(V)` of `s.introduction`
that delimit what its membership gives.

The first is that the finite-energy conclusion genuinely needs a hypothesis on
`V`.  The second is the easy inclusion between the globally-smooth-approximant
reading of the class and the `C^∞(V)`-approximant reading: a globally smooth
approximant is in particular smooth on `V`.  The converse — that a function
smooth on `V` and of finite `H¹_a(V)` norm is approximable by globally smooth
functions — is the Sobolev extension theorem for Lipschitz domains, and is not
proved here.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The domain hypothesis is necessary, not merely convenient

`MemH1a b V u Du` is an *approximability* condition, not a finiteness one: a
globally smooth `u` approximates itself, at distance exactly `0`, whatever its
growth.  On a bounded `V` this costs nothing, because a smooth field has finite
energy there.  On an unbounded `V` it does not: the linear function
`u(x) = x_i` on all of `ℝ^d` lies in `MemH1a` for the identity coefficient
field, and its weighted energy is infinite.  So
`MemH1a b V u Du → sEnergyOn b V Du ≠ ⊤` is **false** without a hypothesis on
`V`, and the boundedness hypothesis of `sEnergyOn_ne_top_of_memH1a` cannot be
dropped. -/

/-- The coordinate gradient of a coordinate projection. -/
theorem smoothGrad_coord (i : Fin d) (x : Vec d) :
    smoothGrad (fun y : Vec d => y i) x = basisVec i := by
  funext j
  simp only [smoothGrad]
  rw [show (fun y : Vec d => y i) =
      ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) from rfl,
    ContinuousLinearMap.fderiv]
  simp [ContinuousLinearMap.proj_apply, basisVec_apply, eq_comm]

/-- Coordinate projections are smooth. -/
theorem contDiff_coord (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y i) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff

/-- The `H¹_s` norm square of the zero pair vanishes. -/
theorem h1sNormSqOn_eq_zero {b : CoeffField d} {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : ∀ x, u x = 0)
    (hD : ∀ x, Du x = 0) : h1sNormSqOn b V u Du = 0 := by
  have h1 : ∀ x : Vec d, ENNReal.ofReal |u x| = 0 := fun x => by simp [hu x]
  have h2 : ∀ x : Vec d,
      ENNReal.ofReal (vecDot (Du x) (matVecMul (symmPart (b x)) (Du x))) = 0 :=
    fun x => by simp [hD x, vecDot, matVecMul]
  simp [h1sNormSqOn, sEnergyOn, h1, h2]

/-- The skew-flux dual norm of the zero field vanishes. -/
theorem skewFluxDualNorm_eq_zero {b : CoeffField d} {V : Set (Vec d)}
    {F : Vec d → Vec d} (hF : ∀ x, F x = 0) : skewFluxDualNorm b V F = 0 := by
  have hzero : ∀ φ : Vec d → ℝ, skewFluxPairing b V F φ = 0 := by
    intro φ
    have hint :
        (fun x => vecDot (smoothGrad φ x) (matVecMul (skewPart (b x)) (F x))) =
          fun _ : Vec d => (0 : ℝ) := by
      funext x
      simp [hF x, vecDot, matVecMul]
    have hI : IntegrableOn
        (fun x => vecDot (smoothGrad φ x) (matVecMul (skewPart (b x)) (F x))) V
        volume := by
      rw [hint]; exact integrableOn_zero
    simp only [skewFluxPairing, ite_eq_left hI, hint]
    simp
  refine le_antisymm (iSup_le fun φ => (hzero φ.1).le) zero_le

/-- The whole space has infinite Lebesgue measure in positive dimension. -/
theorem volume_univ_eq_top (hd : 0 < d) :
    volume (Set.univ : Set (Vec d)) = ⊤ := by
  have huniv : (Set.univ : Set (Vec d)) =
      Set.univ.pi fun _ : Fin d => (Set.univ : Set ℝ) := by
    simp
  rw [huniv, volume_pi_pi]
  simp [Finset.prod_const, ENNReal.top_pow hd.ne']

/-- The identity matrix field is uniformly elliptic with constants `1, 1`. -/
theorem isEllipticMatrix_one_one : IsEllipticMatrix (1 : ℝ) 1 (1 : Mat d) := by
  have hmul : ∀ x : Vec d, matVecMul (1 : Mat d) x = x := by
    intro x
    funext p
    simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
  have hinv : ((1 : Mat d))⁻¹ = 1 := inv_one
  refine ⟨one_pos, le_rfl, fun ξ => ?_, fun ξ => ?_⟩
  · rw [hmul, one_mul]
    exact le_of_eq rfl
  · rw [hinv, hmul, inv_one, one_mul]
    exact le_of_eq rfl

/-- **The unconditional form of the finite-energy statement is false.**  On
`V = ℝ^d` the identity coefficient field and the linear function `u(x) = x_i`
satisfy `MemH1a` while the weighted energy of the gradient is infinite. -/
theorem exists_memH1a_sEnergyOn_eq_top (hd : 0 < d) :
    ∃ (b : CoeffField d) (lam Lam : ℝ) (u : Vec d → ℝ) (Du : Vec d → Vec d),
      0 < lam ∧ lam ≤ Lam ∧ (∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) ∧
        MemH1a b Set.univ u Du ∧ sEnergyOn b Set.univ Du = ⊤ := by
  set i : Fin d := ⟨0, hd⟩ with hidef
  refine ⟨fun _ => (1 : Mat d), 1, 1, fun y => y i, fun _ => basisVec i, one_pos,
    le_rfl, _root_.Filter.Eventually.of_forall fun _ => isEllipticMatrix_one_one, ?_, ?_⟩
  · refine ⟨⟨(contDiff_coord i).continuous.aestronglyMeasurable,
      fun _ => aestronglyMeasurable_const⟩, ?_,
      fun _ => fun y : Vec d => y i, fun _ => contDiff_coord i, ?_, ?_⟩
    · have heq : (fun (x : Vec d) (j : Fin d) =>
          (fderiv ℝ (fun y : Vec d => y i) x) (basisVec j)) =
            fun _ : Vec d => basisVec i := funext fun x => smoothGrad_coord i x
      rw [← heq]
      exact HasWeakGradientOn.of_contDiff ((contDiff_coord i).of_le (by simp))
    · refine tendsto_const_nhds.congr fun n => ?_
      exact (h1sNormSqOn_eq_zero (b := fun _ => (1 : Mat d)) (fun x => by simp)
        (fun x => by simp [smoothGrad_coord i x])).symm
    · refine tendsto_const_nhds.congr fun n => ?_
      exact (skewFluxDualNorm_eq_zero (b := fun _ => (1 : Mat d))
        (fun x => by simp [smoothGrad_coord i x])).symm
  · have hs : symmPart (1 : Mat d) = 1 := by
      funext p q
      by_cases h : p = q <;> simp [symmPart, Matrix.one_apply, h, eq_comm]
    have hmul : ∀ x : Vec d, matVecMul (1 : Mat d) x = x := by
      intro x
      funext p
      simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
    have hconst :
        vecDot (basisVec i) (matVecMul (symmPart (1 : Mat d)) (basisVec i))
          = 1 := by
      rw [hs, hmul]
      exact vecNormSq_basisVec i
    simp only [sEnergyOn]
    rw [setLIntegral_const, hconst, ENNReal.ofReal_one, one_mul,
      volume_univ_eq_top hd]

/-! ## Smoothness on `V`, the easy inclusion

The globally-smooth-approximant class embeds in what a `C^∞(V)`-approximant
class would give: the restriction of a globally smooth function to `V` is
smooth on `V`.  The converse — that a function smooth on `V` and of finite
`H¹_a(V)` norm is approximable by globally smooth functions — is the Sobolev
extension theorem for Lipschitz domains and is a carried obligation, not proved
here. -/

/-- **The easy inclusion.**  A globally smooth approximant is in particular
smooth on `V`. -/
theorem contDiffOn_of_contDiff {V : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiffOn ℝ (⊤ : ℕ∞) f V :=
  hf.contDiffOn

/-- **The easy inclusion, at the level of the approximating sequence.**
Every `MemH1a` witness is a sequence that is smooth on `V`, with the same two
convergences; so the globally-smooth class is contained in the
`C^∞(V)`-approximant class. -/
theorem memH1a_approximants_contDiffOn {b : CoeffField d} {V : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d} (hu : MemH1a b V u Du) :
    ∃ v : ℕ → Vec d → ℝ,
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (v n) V) ∧
      _root_.Filter.Tendsto
        (fun n => h1sNormSqOn b V (fun x => v n x - u x)
          (fun x => smoothGrad (v n) x - Du x)) _root_.Filter.atTop (nhds 0) ∧
      _root_.Filter.Tendsto
        (fun n => skewFluxDualNorm b V (fun x => smoothGrad (v n) x - Du x))
        _root_.Filter.atTop (nhds 0) := by
  obtain ⟨-, -, v, hv, h1, h2⟩ := hu
  exact ⟨v, fun n => contDiffOn_of_contDiff (hv n), h1, h2⟩

end

end HighContrast
end HCPolySupport
