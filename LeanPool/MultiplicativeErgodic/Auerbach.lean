/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.Complemented
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Choose

/-!
# Auerbach's lemma and the projection bound it gives

Mathlib has no Auerbach lemma. It is needed in three places here: to condition an arbitrary
`k`-dimensional subspace uniformly (`ProofMet.Grassmannian`, completeness), to produce a bounded
projection onto a finite-dimensional subspace (`Submodule.closedComplemented_of_finiteDimensional`
below), and in the comparison of volume growth with the Bernstein numbers
(`ProofMet.GrowthFunction`).
-/

@[expose] public section

namespace MultiplicativeErgodic

open Module _root_.Submodule

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A conditioned family is in particular linearly independent. -/
theorem linearIndependent_of_norm_coeff_le {k : ℕ} {v : Fin k → X} {C : ℝ}
    (h : ∀ a : Fin k → ℝ, ‖a‖ ≤ C * ‖∑ i, a i • v i‖) : LinearIndependent ℝ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hb := h g
  rw [hg, norm_zero, mul_zero] at hb
  have hg0 : g = 0 := norm_eq_zero.mp (le_antisymm hb (norm_nonneg g))
  simp [hg0]

/-- **Auerbach's lemma.** A `k`-dimensional real normed space has a basis of unit vectors whose
coordinate functionals all have norm `1`, i.e. `‖a‖_∞ ≤ ‖∑ aᵢ eᵢ‖` for every coefficient vector.
The conditioning constant is `1`, and in particular does not depend on the space. -/
theorem exists_auerbach_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {k : ℕ} (hk : Module.finrank ℝ E = k) :
    ∃ e : Fin k → E, (∀ i, ‖e i‖ = 1) ∧ ∀ a : Fin k → ℝ, ‖a‖ ≤ ‖∑ i, a i • e i‖ := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · refine ⟨fun i => i.elim0, fun i => i.elim0, fun a => ?_⟩
    simp [Subsingleton.elim a 0]
  set b : Module.Basis (Fin k) ℝ E := Module.finBasisOfFinrankEq ℝ E hk with hb
  set D : E [⋀^Fin k]→ₗ[ℝ] ℝ := b.det with hD
  set K : Set (Fin k → E) := Set.univ.pi fun _ => Metric.sphere (0 : E) 1 with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_sphere _ _
  have hmemK : ∀ y : Fin k → E, y ∈ K ↔ ∀ i, ‖y i‖ = 1 := by
    intro y
    simp [hK, ]
  -- the normalised basis is a competitor with nonzero determinant
  have hbne : ∀ i, ‖b i‖ ≠ 0 := fun i => norm_ne_zero_iff.mpr (b.ne_zero i)
  set u : Fin k → E := fun i => ‖b i‖⁻¹ • b i with hu
  have huK : u ∈ K := (hmemK u).mpr fun i => by
    rw [hu]
    simp only [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hbne i)
  have hDu : D u = ∏ i, ‖b i‖⁻¹ := by
    rw [hu, hD]
    rw [show (fun i => ‖b i‖⁻¹ • b i) = (fun i => ‖b i‖⁻¹ • (b : Fin k → E) i) from rfl]
    rw [AlternatingMap.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one]
  have hDupos : 0 < |D u| := by
    rw [hDu, abs_of_pos]
    · exact Finset.prod_pos fun i _ =>
        inv_pos.mpr (lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hbne i)))
    · exact Finset.prod_pos fun i _ =>
        inv_pos.mpr (lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hbne i)))
  -- maximise |det| over the compact set of unit tuples
  have hcont : Continuous fun y : Fin k → E => |D y| := by
    refine continuous_abs.comp ?_
    have hdet : Continuous fun y : Fin k → E => (b.toMatrix y).det := by
      refine Continuous.matrix_det ?_
      refine continuous_pi fun i => continuous_pi fun j => ?_
      have hent : (fun y : Fin k → E => b.toMatrix y i j) = fun y => b.coord i (y j) := by
        funext y; rw [Basis.toMatrix_apply, Basis.coord_apply]
      rw [hent]
      exact ((b.coord i).continuous_of_finiteDimensional).comp (continuous_apply j)
    exact hdet.congr fun y => by rw [hD]; exact (b.det_apply y).symm
  obtain ⟨e, heK, hemax⟩ := hKc.exists_isMaxOn ⟨u, huK⟩ hcont.continuousOn
  have henorm : ∀ i, ‖e i‖ = 1 := (hmemK e).mp heK
  have hDe : 0 < |D e| := lt_of_lt_of_le hDupos (hemax huK)
  have hlin : ∀ (i : Fin k) (x : E),
      D (Function.update e i x) = D.toMultilinearMap.toLinearMap e i x := fun i x => rfl
  -- `|det|` is maximal at `e`, so every coordinate functional has norm at most one
  have hbound : ∀ (i : Fin k) (x : E), |D (Function.update e i x)| ≤ |D e| * ‖x‖ := by
    intro i x
    rcases eq_or_ne x 0 with rfl | hx
    · rw [hlin, map_zero]
      simp
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hyK : Function.update e i (‖x‖⁻¹ • x) ∈ K := by
      refine (hmemK _).mpr fun j => ?_
      rcases eq_or_ne j i with rfl | hj
      · rw [Function.update_self, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hxpos)]
      · rw [Function.update_of_ne hj]; exact henorm j
    have hmax : |D (Function.update e i (‖x‖⁻¹ • x))| ≤ |D e| := hemax hyK
    have hsm : D (Function.update e i (‖x‖⁻¹ • x)) = ‖x‖⁻¹ * D (Function.update e i x) := by
      rw [hlin, hlin, map_smul, smul_eq_mul]
    rw [hsm, abs_mul, abs_inv, abs_of_pos hxpos, inv_mul_le_iff₀ hxpos] at hmax
    linarith [hmax]
  refine ⟨e, henorm, fun a => ?_⟩
  set x : E := ∑ i, a i • e i with hx
  have hcoord : ∀ i, D (Function.update e i x) = a i * D e := by
    intro i
    rw [hlin, hx, map_sum]
    have hterm : ∀ j : Fin k, D.toMultilinearMap.toLinearMap e i (a j • e j)
        = if j = i then a i * D e else 0 := by
      intro j
      rw [map_smul, smul_eq_mul, ← hlin]
      rcases eq_or_ne j i with rfl | hj
      · rw [ite_eq_left rfl, Function.update_eq_self]
      · rw [ite_eq_right hj]
        have hzero : D (Function.update e i (e j)) = 0 := by
          refine D.map_eq_zero_of_eq _ (i := i) (j := j) ?_ (Ne.symm hj)
          rw [Function.update_self, Function.update_of_ne hj]
        rw [hzero, mul_zero]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq' Finset.univ i]
    simp
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => ?_
  have h1 := hbound i x
  rw [hcoord i, abs_mul] at h1
  have h2 : |a i| * |D e| ≤ |D e| * ‖x‖ := h1
  have h3 : |a i| ≤ ‖x‖ := by
    rw [mul_comm] at h2
    exact le_of_mul_le_mul_left h2 hDe
  simpa [Real.norm_eq_abs] using h3

/-- **Auerbach projection.** Every `m`-dimensional subspace of a normed space is the range of a
continuous projection of norm at most `m`. The bound comes from an Auerbach basis, whose
coordinate functionals have norm `1`; Hahn-Banach extends them to the whole space. -/
theorem exists_proj_norm_le (W : Submodule ℝ X) [FiniteDimensional ℝ W] {m : ℕ}
    (hm : Module.finrank ℝ W = m) :
    ∃ P : X →L[ℝ] X, (∀ x, P x ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ‖P‖ ≤ m := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · have hbot : W = ⊥ := Submodule.finrank_eq_zero.mp hm
    refine ⟨0, fun x => by simp [hbot], fun w hw => ?_, by simp⟩
    rw [hbot, Submodule.mem_bot] at hw
    simp [hw]
  have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hmpos⟩
  obtain ⟨e, henorm, hcond⟩ := exists_auerbach_basis (E := (W : Submodule ℝ X)) hm
  have hind : LinearIndependent ℝ e :=
    linearIndependent_of_norm_coeff_le (C := 1) (fun a => by simpa using hcond a)
  have : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  set b : Module.Basis (Fin m) ℝ (W : Submodule ℝ X) :=
    basisOfLinearIndependentOfCardEqFinrank hind (by simp [hm]) with hb
  have hbe : ⇑b = e := coe_basisOfLinearIndependentOfCardEqFinrank hind (by simp [hm])
  -- the coordinate functionals have norm at most one
  have hcoord : ∀ (i : Fin m) (w : (W : Submodule ℝ X)), |b.coord i w| ≤ ‖w‖ := by
    intro i w
    have hsum : ∑ j, b.equivFun w j • e j = w := by
      rw [← hbe]; exact b.sum_equivFun w
    have h1 : |b.equivFun w i| ≤ ‖b.equivFun w‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (b.equivFun w) i
    have h2 : ‖b.equivFun w‖ ≤ ‖∑ j, b.equivFun w j • e j‖ := hcond _
    rw [hsum] at h2
    have h3 : b.coord i w = b.equivFun w i := by simp [Basis.coord_apply, Basis.equivFun_apply]
    rw [h3]
    linarith
  -- bundle them as continuous functionals and extend by Hahn-Banach
  have hex : ∀ i : Fin m, ∃ g : X →L[ℝ] ℝ,
      (∀ w : (W : Submodule ℝ X), g (w : X) = b.coord i w) ∧ ‖g‖ ≤ 1 := by
    intro i
    set f : (W : Submodule ℝ X) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i) with hf
    have hfnorm : ‖f‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
      rw [one_mul, hf]
      simpa [Real.norm_eq_abs] using hcoord i w
    obtain ⟨g, hgext, hgnorm⟩ := exists_extension_norm_eq (W : Submodule ℝ X) f
    exact ⟨g, fun w => hgext w, by rw [hgnorm]; exact hfnorm⟩
  choose g hgext hgnorm using hex
  refine ⟨∑ i, (g i).smulRight ((e i : X)), ?_, ?_, ?_⟩
  · intro x
    simp only [FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (e i).2
  · intro w hw
    simp only [FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply]
    have hgw : ∀ i, g i w = b.coord i ⟨w, hw⟩ := fun i => hgext i ⟨w, hw⟩
    have : ∑ i, (g i) w • (e i : X) =
        ((∑ i, b.coord i ⟨w, hw⟩ • e i : (W : Submodule ℝ X)) : X) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [hgw i]
    rw [this]
    have : ∑ i, b.coord i ⟨w, hw⟩ • e i = ∑ i, b.equivFun ⟨w, hw⟩ i • b i := by
      rw [hbe]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Basis.coord_apply, Basis.equivFun_apply]
    rw [this, b.sum_equivFun]
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    calc ‖(∑ i, (g i).smulRight ((e i : X))) x‖
        = ‖∑ i, (g i) x • (e i : X)‖ := by
          simp only [FunLike.coe_sum, Finset.sum_apply,
            ContinuousLinearMap.smulRight_apply]
      _ ≤ ∑ i, ‖(g i) x • (e i : X)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin m, ‖x‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          have h1 : |(g i) x| ≤ ‖x‖ := by
            have := (g i).le_opNorm x
            have h2 := hgnorm i
            calc |(g i) x| = ‖(g i) x‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖g i‖ * ‖x‖ := (g i).le_opNorm x
              _ ≤ 1 * ‖x‖ := by nlinarith [norm_nonneg x]
              _ = ‖x‖ := one_mul _
          have h2 : ‖(e i : X)‖ = 1 := by
            have := henorm i
            simpa using this
          rw [h2, mul_one]
          exact h1
      _ = m * ‖x‖ := by simp [Finset.sum_const]

/-- Finite-dimensional subspaces are complemented, with a projection of norm at most the
dimension. This closes `GrassmannianFin.closedComplemented`. -/
theorem Submodule.closedComplemented_of_finiteDimensional (W : Submodule ℝ X)
    [FiniteDimensional ℝ W] : W.ClosedComplemented := by
  obtain ⟨P, hmem, hid, -⟩ := exists_proj_norm_le W (m := Module.finrank ℝ W) rfl
  exact ⟨P.codRestrict W hmem, fun w => Subtype.ext (hid (w : X) w.2)⟩

/-- **A subspace cannot be uniformly close to one of smaller dimension.** If `finrank W < finrank A`
then some unit vector of `A` is at distance at least `1/(1 + finrank W)` from `W`.

This is the quantitative form of "dimension cannot drop", and it is what repairs the appeal to
Gohberg–Krein in `gonzalez2015concise`, Lemma 5: that argument wants a unit `u ∈ A` with
`d(u, W) = 1` exactly, which needs `W ≤ A` and is unavailable when `W ⊄ A`. A constant loss is
harmless there, since the conclusion is only claimed up to constants depending on `k`. -/
theorem exists_unit_far_of_finrank_lt {A W : Submodule ℝ X}
    [FiniteDimensional ℝ W] (h : Module.finrank ℝ W < Module.finrank ℝ A) :
    ∃ u ∈ A, ‖u‖ = 1 ∧ (1 : ℝ) / (1 + Module.finrank ℝ W) ≤ Metric.infDist u (W : Set X) := by
  classical
  obtain ⟨P, hmem, hid, hnorm⟩ := exists_proj_norm_le W (m := Module.finrank ℝ W) rfl
  set m : ℕ := Module.finrank ℝ W with hmdef
  by_contra hcon
  push Not at hcon
  -- every unit vector of `A` is within `1/(1+m)` of `W`, so `P` is injective on `A`
  have hinj : Function.Injective ((P.codRestrict W hmem).toLinearMap.domRestrict A) := by
    rw [LinearMap.injective_domRestrict_iff, Submodule.disjoint_def]
    intro x hxA hxker
    by_contra hx0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hPx : P x = 0 := by
      have : (P.codRestrict W hmem) x = 0 := hxker
      exact congrArg Subtype.val this
    set u : X := ‖x‖⁻¹ • x with hu
    have huA : u ∈ A := A.smul_mem _ hxA
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hxpos)]
    have hPu : P u = 0 := by rw [hu, map_smul, hPx, smul_zero]
    have hlt := hcon u huA hunorm
    -- pick `w ∈ W` nearly realising the distance
    obtain ⟨w, hwW, hwlt⟩ := (Metric.infDist_lt_iff ⟨0, W.zero_mem⟩).mp hlt
    have hkey : ‖u - P u‖ ≤ (1 + ‖P‖) * ‖u - w‖ := by
      have hsub : u - P u = (u - w) - P (u - w) := by
        rw [map_sub, hid w hwW]; abel
      calc ‖u - P u‖ = ‖(u - w) - P (u - w)‖ := by rw [hsub]
        _ ≤ ‖u - w‖ + ‖P (u - w)‖ := norm_sub_le _ _
        _ ≤ ‖u - w‖ + ‖P‖ * ‖u - w‖ := by gcongr; exact P.le_opNorm _
        _ = (1 + ‖P‖) * ‖u - w‖ := by ring
    rw [hPu, sub_zero, hunorm] at hkey
    have hdist : ‖u - w‖ < 1 / (1 + m) := by rwa [← dist_eq_norm]
    have hPnn : (0:ℝ) ≤ ‖P‖ := norm_nonneg P
    have hmnn : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hpos : (0:ℝ) < 1 + (m : ℝ) := by linarith
    have h1 : (1 + ‖P‖) * ‖u - w‖ ≤ (1 + (m:ℝ)) * ‖u - w‖ := by
      have hnn : (0:ℝ) ≤ ‖u - w‖ := norm_nonneg _
      nlinarith
    have h2 : (1 + (m:ℝ)) * ‖u - w‖ < 1 := by
      have hmul := mul_lt_mul_of_pos_left hdist hpos
      rwa [mul_one_div, div_self (ne_of_gt hpos)] at hmul
    linarith
  have hle : Module.finrank ℝ A ≤ Module.finrank ℝ W :=
    LinearMap.finrank_le_finrank_of_injective hinj
  omega

end MultiplicativeErgodic
