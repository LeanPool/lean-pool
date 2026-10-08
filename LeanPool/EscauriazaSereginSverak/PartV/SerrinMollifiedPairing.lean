/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSlab
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinProductRule
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinFubini

/-!
# Mollified pairings as primitives of their fluxes

For a smooth compactly supported kernel `ρ`, the mollified component
`y ↦ ∫ u(x,t)_k ρ(y - x) dx` is, at every point `y`, the primitive in time of the
momentum flux tested against `ρ(y - ·)`. This is the pointwise-in-space
calculus behind the cross-testing identity of `lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The mollified `k`th component of the time slice at time `t`, evaluated at `y`. -/
@[expose] def serrinMol (u : ParabolicPoint → Vec3) (ρ : Vec3 → ℝ) (k : Fin 3) (y : Vec3)
    (t : ℝ) : ℝ :=
  ∫ x : Vec3, u (x, t) k * ρ (y - x)

/-- The momentum flux density tested against the translated kernel `ρ(y - ·)`
in the `k`th component. -/
@[expose] def serrinMolFluxDensity (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
    (ρ : Vec3 → ℝ) (k : Fin 3) (y : Vec3) (z : ParabolicPoint) : ℝ :=
  -(∑ j : Fin 3, u z k * u z j * spatialDeriv ρ j (y - z.1))
    + (∑ j : Fin 3, Du z k j * spatialDeriv ρ j (y - z.1))
    - p z * spatialDeriv ρ k (y - z.1)

/-- The spatially integrated flux of the mollified `k`th component. -/
@[expose] def serrinMolFlux (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
    (ρ : Vec3 → ℝ) (k : Fin 3) (y : Vec3) (τ : ℝ) : ℝ :=
  ∫ x : Vec3, serrinMolFluxDensity u Du p ρ k y (x, τ)

/-- The translated and reflected kernel placed in the `k`th component. -/
@[expose] def serrinKernelTest (ρ : Vec3 → ℝ) (k : Fin 3) (y : Vec3) : Vec3 → Vec3 :=
  fun x i => if i = k then ρ (y - x) else 0

theorem spatialDeriv_reflect {ρ : Vec3 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (y : Vec3) (j : Fin 3) (x : Vec3) :
    spatialDeriv (fun x' => ρ (y - x')) j x = -spatialDeriv ρ j (y - x) := by
  have hd : HasFDerivAt (fun x' => ρ (y - x'))
      ((fderiv ℝ ρ (y - x)).comp (-ContinuousLinearMap.id ℝ Vec3)) x := by
    have hin : HasFDerivAt (fun x' : Vec3 => y - x') (-ContinuousLinearMap.id ℝ Vec3) x :=
      (hasFDerivAt_id x).const_sub y
    exact ((hρ.differentiable (by simp)) (y - x)).hasFDerivAt.comp x hin
  simp only [spatialDeriv, hd.fderiv, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.id_apply, map_neg]

private theorem serrinKernelTest_component (ρ : Vec3 → ℝ) (k : Fin 3) (y : Vec3)
    (i : Fin 3) :
    (fun x => serrinKernelTest ρ k y x i) =
      if i = k then (fun x => ρ (y - x)) else (fun _ => 0) := by
  by_cases h : i = k
  · simp [serrinKernelTest, h]
  · simp [serrinKernelTest, h]

theorem serrinKernelTest_contDiff {ρ : Vec3 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (k : Fin 3) (y : Vec3) :
    ContDiff ℝ (⊤ : ℕ∞) (serrinKernelTest ρ k y) := by
  apply contDiff_pi.mpr
  intro i
  rw [serrinKernelTest_component]
  split_ifs
  · exact hρ.comp (contDiff_const.sub contDiff_id)
  · exact contDiff_const

theorem serrinKernelTest_hasCompactSupport {ρ : Vec3 → ℝ}
    (hρc : HasCompactSupport ρ) (k : Fin 3) (y : Vec3) :
    HasCompactSupport (serrinKernelTest ρ k y) := by
  have hrefl : HasCompactSupport (fun x : Vec3 => ρ (y - x)) := by
    have h := hρc.comp_homeomorph (Homeomorph.subLeft y)
    exact h
  apply HasCompactSupport.of_support_subset_isCompact hrefl.isCompact
  intro x hx
  apply subset_tsupport
  intro hzero
  apply hx
  funext i
  simp [serrinKernelTest, hzero]

theorem serrinFlux_kernelTest {ρ : Vec3 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (k : Fin 3) (y : Vec3) (z : ParabolicPoint) :
    serrinFlux u Du p (serrinKernelTest ρ k y) z =
      serrinMolFluxDensity u Du p ρ k y z := by
  have hder (i j : Fin 3) :
      spatialDeriv (fun x => serrinKernelTest ρ k y x i) j z.1 =
        if i = k then -spatialDeriv ρ j (y - z.1) else 0 := by
    rw [serrinKernelTest_component]
    split_ifs
    · exact spatialDeriv_reflect hρ y j z.1
    · simp [spatialDeriv]
  simp only [serrinFlux, serrinMolFluxDensity, hder]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_comm (γ := Fin 3) (f := fun i j => if i = k then _ else _)]
  simp only [Fin.sum_univ_three]
  fin_cases k <;> simp <;> ring

theorem serrinPairing_kernelTest (u : ParabolicPoint → Vec3) (ρ : Vec3 → ℝ)
    (k : Fin 3) (y : Vec3) (x : Vec3) (t : ℝ) :
    (∑ i : Fin 3, u (x, t) i * serrinKernelTest ρ k y x i) = u (x, t) k * ρ (y - x) := by
  simp [serrinKernelTest]

/-- The mollified component of a finite-energy weak solution is, at every
point, the primitive of its tested flux. -/
theorem serrinMol_slab
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hU : IsSerrinWeakSolution T a u Du p)
    {ρ : Vec3 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (k : Fin 3) (y : Vec3) :
    IntegrableOn (serrinMolFlux u Du p ρ k y) (Ioo 0 T) ∧
    ∀ t ∈ Icc 0 T, serrinMol u ρ k y t =
      serrinMol u ρ k y 0 + ∫ τ in (0 : ℝ)..t, serrinMolFlux u Du p ρ k y τ := by
  obtain ⟨hint, hslab⟩ := serrin_slab_identity hU
    (serrinKernelTest_contDiff hρ k y) (serrinKernelTest_hasCompactSupport hρc k y)
  have hflux : (fun τ => ∫ x : Vec3,
      serrinFlux u Du p (serrinKernelTest ρ k y) (x, τ)) = serrinMolFlux u Du p ρ k y := by
    funext τ
    simp only [serrinMolFlux]
    congr 1
    funext x
    exact serrinFlux_kernelTest hρ u Du p k y (x, τ)
  have hpair (t : ℝ) : (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * serrinKernelTest ρ k y x i) =
      serrinMol u ρ k y t := by
    simp only [serrinMol, serrinPairing_kernelTest]
  rw [hflux] at hint hslab
  refine ⟨hint, fun t ht => ?_⟩
  have h := hslab t ht
  rwa [hpair, hpair] at h

/-- The product of two mollified components is the primitive of the product
rule expression. -/
theorem serrinMol_product
    {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3} {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu) (hV : IsSerrinWeakSolution T b v Dv pv)
    {ρ : Vec3 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (k : Fin 3) (y : Vec3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    serrinMol v ρ k y t * serrinMol u ρ k y t =
      serrinMol v ρ k y 0 * serrinMol u ρ k y 0 +
        ∫ τ in (0 : ℝ)..t, (serrinMolFlux v Dv pv ρ k y τ * serrinMol u ρ k y τ +
          serrinMol v ρ k y τ * serrinMolFlux u Du pu ρ k y τ) := by
  obtain ⟨hvi, hvs⟩ := serrinMol_slab hV hρ hρc k y
  obtain ⟨hui, hus⟩ := serrinMol_slab hU hρ hρc k y
  exact serrin_primitive_product hvi hui hvs hus ht

end ESS
