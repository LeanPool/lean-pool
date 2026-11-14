/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.BoundedMeasurableLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ContinuousCoeffLimit
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.Minimal

/-!
# ResolventIdentity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Resolvent identity for the analytic cubic supremum

The bounded-domain resolvent identity is passed through the cubic exhaustion.
The only analytic continuity input is the already proved convergence of
interior representatives along uniformly bounded pointwise-convergent data.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Topology
open MarkovProcess.Semigroup
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- The real local cube resolvents increase to the real value of their
extended-real supremum on nonnegative bounded data. -/
theorem tendsto_analyticCubeResolvent (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    Tendsto (fun m => A.analyticCubeResolvent mu f hf hfD m x) atTop
      (nhds (A.analyticMinimalResolvent mu f hf hfD x).toReal) := by
  have hmono := A.monotone_analyticCubeResolvent mu hf hf0 hfD x
  have hbdd : BddAbove (Set.range fun m =>
      A.analyticCubeResolvent mu f hf hfD m x) := by
    refine ⟨D / (mu : ℝ), ?_⟩
    rintro y ⟨m, rfl⟩
    have habs := A.abs_analyticCubeResolvent_le mu hf hD hfD m x
    exact (le_abs_self _).trans habs
  have hsup : (A.analyticMinimalResolvent mu f hf hfD x).toReal =
      ⨆ m, A.analyticCubeResolvent mu f hf hfD m x := by
    rw [analyticMinimalResolvent]
    change (⨆ m, ENNReal.ofReal
      (A.analyticCubeResolvent mu f hf hfD m x)).toReal = _
    rw [ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
    apply iSup_congr
    intro m
    rw [ENNReal.toReal_ofReal
      (A.analyticCubeResolvent_nonneg mu hf hf0 hfD m x)]
  rw [hsup]
  exact tendsto_atTop_ciSup hmono hbdd

/-- Applying a fixed outer cube resolvent commutes with the monotone limit of
the inner cubic exhaustion. -/
theorem tendsto_analyticCubeResolvent_comp (mu nu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D)
    (outer : ℕ) (x : Vec d) :
    let g : Vec d → ℝ := fun y =>
      (A.analyticMinimalResolvent mu f hf hfD y).toReal
    Tendsto (fun k => A.analyticCubeResolvent nu
        (A.analyticCubeResolvent mu f hf hfD k)
        (A.measurable_analyticCubeResolvent mu hf hfD k)
        (D := D / (mu : ℝ))
        (A.abs_analyticCubeResolvent_le mu hf hD hfD k) outer x) atTop
      (nhds (A.analyticCubeResolvent nu g
        (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal
        (D := D / (mu : ℝ)) (fun y => by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_le_of_le_ofReal
            (div_nonneg hD mu.property.le)
            (A.analyticMinimalResolvent_le mu hf hf0 hD hfD y)) outer x)) := by
  dsimp only
  by_cases hx : x ∈ wholeSpaceCube d outer
  · let hU := isOpenBoundedConvexDomain_wholeSpaceCube d outer
    let gk : ℕ → Vec d → ℝ := fun k =>
      A.analyticCubeResolvent mu f hf hfD k
    let g : Vec d → ℝ := fun y =>
      (A.analyticMinimalResolvent mu f hf hfD y).toReal
    let hg : Measurable g :=
      (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal
    let C : ℝ := D / (mu : ℝ)
    have hC : 0 ≤ C := div_nonneg hD mu.property.le
    have hgkBound : ∀ k y, |gk k y| ≤ C := fun k y =>
      A.abs_analyticCubeResolvent_le mu hf hD hfD k y
    have hg0 : ∀ y, 0 ≤ g y := fun _ => ENNReal.toReal_nonneg
    have hgBound : ∀ y, |g y| ≤ C := by
      intro y
      rw [abs_of_nonneg (hg0 y)]
      exact ENNReal.toReal_le_of_le_ofReal hC
        (A.analyticMinimalResolvent_le mu hf hf0 hD hfD y)
    let Fk : ℕ → ScalarL2 (wholeSpaceCube d outer) := fun k =>
      boundedMeasurableToScalarL2 hU
        ((A.measurable_analyticCubeResolvent mu hf hfD k).comp
          measurable_subtype_coe) (fun y => hgkBound k y)
    let Fl : ScalarL2 (wholeSpaceCube d outer) :=
      boundedMeasurableToScalarL2 hU (hg.comp measurable_subtype_coe)
        (fun y => hgBound y)
    have hpt : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d outer),
        Tendsto (fun k => Fk k y) atTop (nhds (Fl y)) := by
      have hFk : ∀ k, Fk k =ᵐ[volumeMeasureOn (wholeSpaceCube d outer)]
          domainExtension (gk k ∘ Subtype.val) := fun k =>
        boundedMeasurableToScalarL2_coeFn hU
          ((A.measurable_analyticCubeResolvent mu hf hfD k).comp
            measurable_subtype_coe) (fun y => hgkBound k y)
      have hFl := boundedMeasurableToScalarL2_coeFn hU
        (hg.comp measurable_subtype_coe) (fun y => hgBound y)
      filter_upwards [ae_all_iff.2 hFk, hFl,
        ae_restrict_mem hU.isOpen.measurableSet] with y hyk hyl hyU
      rw [hyl, domainExtension_of_mem hyU]
      have ht := A.tendsto_analyticCubeResolvent mu hf hf0 hD hfD y
      apply ht.congr'
      filter_upwards with k
      rw [hyk k, domainExtension_of_mem hyU]
      rfl
    have hdiff : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d outer),
        ∀ k, |Fk k y - Fl y| ≤ 2 * C := by
      have hFk : ∀ k, Fk k =ᵐ[volumeMeasureOn (wholeSpaceCube d outer)]
          domainExtension (gk k ∘ Subtype.val) := fun k =>
        boundedMeasurableToScalarL2_coeFn hU
          ((A.measurable_analyticCubeResolvent mu hf hfD k).comp
            measurable_subtype_coe) (fun y => hgkBound k y)
      have hFl := boundedMeasurableToScalarL2_coeFn hU
        (hg.comp measurable_subtype_coe) (fun y => hgBound y)
      filter_upwards [ae_all_iff.2 hFk, hFl,
        ae_restrict_mem hU.isOpen.measurableSet] with y hyk hyl hyU
      intro k
      rw [hyk k, hyl, domainExtension_of_mem hyU,
        domainExtension_of_mem hyU]
      calc
        |gk k y - g y| ≤ |gk k y| + |g y| := abs_sub _ _
        _ ≤ C + C := add_le_add (hgkBound k y) (hgBound y)
        _ = 2 * C := by ring
    have hnorm : Tendsto (fun k => ‖Fk k - Fl‖) atTop (nhds 0) :=
      tendsto_norm_scalarL2_sub_of_bounded_ae_tendsto hU hdiff hpt
    have hdiff' : ∀ k, ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d outer),
        |Fk k y - Fl y| ≤ 2 * C := fun k => hdiff.mono fun _ hy => hy k
    exact tendsto_representative_of_tendsto_norm_continuousCoeff A.a hU
      nu.property A.hnu (A.cubeEllipticity outer) A.hsymm
      (A.skewContinuousOnCube outer) A.hd
      (M := 2 * C) (mul_nonneg (by norm_num) hC) hdiff' hnorm
      (fun k => A.continuousOn_analyticCubeResolvent nu
        (A.measurable_analyticCubeResolvent mu hf hfD k)
        (A.abs_analyticCubeResolvent_le mu hf hD hfD k) outer)
      (fun k => A.analyticCubeResolvent_ae nu
        (A.measurable_analyticCubeResolvent mu hf hfD k)
        (A.abs_analyticCubeResolvent_le mu hf hD hfD k) outer)
      (A.continuousOn_analyticCubeResolvent nu hg (fun y => hgBound y) outer)
      (A.analyticCubeResolvent_ae nu hg (fun y => hgBound y) outer) hx
  · simp only [analyticCubeResolvent, dite_eq_right hx]
    exact tendsto_const_nhds

/-- The bounded-domain identity in the orientation used by the abstract
minimal-resolvent interface. -/
theorem analyticCubeResolvent_resolventEquation (lam mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    A.analyticCubeResolvent lam f hf hfD m x =
      A.analyticCubeResolvent mu f hf hfD m x +
        ((mu : ℝ) - (lam : ℝ)) *
          A.analyticCubeResolvent lam
            (A.analyticCubeResolvent mu f hf hfD m)
            (A.measurable_analyticCubeResolvent mu hf hfD m)
            (D := D / (mu : ℝ))
            (A.abs_analyticCubeResolvent_le mu hf hD hfD m) m x := by
  have h := A.analyticCubeResolvent_resolvent_identity mu lam hf hD hfD m x
  linarith only [h]

/-- The diagonal of the two cubic exhaustions computes the composition of
the two analytic minimal resolvents on nonnegative bounded data. -/
theorem analyticMinimalResolvent_comp_eq_iSup (lam mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    let g : Vec d → ℝ := fun y ↦
      (A.analyticMinimalResolvent mu f hf hfD y).toReal
    (A.analyticMinimalResolvent lam g
        (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal
        (D := D / (mu : ℝ)) (fun y ↦ by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_le_of_le_ofReal
            (div_nonneg hD mu.property.le)
            (A.analyticMinimalResolvent_le mu hf hf0 hD hfD y)) x).toReal =
      ⨆ n, A.analyticCubeResolvent lam
        (A.analyticCubeResolvent mu f hf hfD n)
        (A.measurable_analyticCubeResolvent mu hf hfD n)
        (D := D / (mu : ℝ))
        (A.abs_analyticCubeResolvent_le mu hf hD hfD n) n x := by
  dsimp only
  let gk : ℕ → Vec d → ℝ := fun k ↦
    A.analyticCubeResolvent mu f hf hfD k
  let g : Vec d → ℝ := fun y ↦
    (A.analyticMinimalResolvent mu f hf hfD y).toReal
  let C : ℝ := D / (mu : ℝ)
  have hC : 0 ≤ C := div_nonneg hD mu.property.le
  have hgk0 : ∀ k y, 0 ≤ gk k y := fun k y ↦
    A.analyticCubeResolvent_nonneg mu hf hf0 hfD k y
  have hg0 : ∀ y, 0 ≤ g y := fun _ ↦ ENNReal.toReal_nonneg
  have hgkBound : ∀ k y, |gk k y| ≤ C := fun k y ↦
    A.abs_analyticCubeResolvent_le mu hf hD hfD k y
  have hgBound : ∀ y, |g y| ≤ C := by
    intro y
    rw [abs_of_nonneg (hg0 y)]
    exact ENNReal.toReal_le_of_le_ofReal hC
      (A.analyticMinimalResolvent_le mu hf hf0 hD hfD y)
  let a : ℕ → ℕ → ℝ := fun n k ↦
    A.analyticCubeResolvent lam (gk k)
      (A.measurable_analyticCubeResolvent mu hf hfD k) (hgkBound k) n x
  have haMonoLeft : ∀ k, Monotone fun n ↦ a n k := by
    intro k
    exact A.monotone_analyticCubeResolvent lam
      (A.measurable_analyticCubeResolvent mu hf hfD k) (hgk0 k)
      (hgkBound k) x
  have hgkMono : Monotone gk := by
    intro i j hij y
    exact A.monotone_analyticCubeResolvent mu hf hf0 hfD y hij
  have haMonoRight : ∀ n, Monotone (a n) := by
    intro n i j hij
    exact A.analyticCubeResolvent_mono lam
      (A.measurable_analyticCubeResolvent mu hf hfD i)
      (A.measurable_analyticCubeResolvent mu hf hfD j)
      (hgkBound i) (hgkBound j) (hgkMono hij) n x
  have haBdd : ∀ n, BddAbove (Set.range (a n)) := by
    intro n
    refine ⟨C / (lam : ℝ), ?_⟩
    rintro y ⟨k, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticCubeResolvent_le lam
        (A.measurable_analyticCubeResolvent mu hf hfD k) hC
        (hgkBound k) n x)
  have hrow : ∀ n,
      A.analyticCubeResolvent lam g
          (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal
          (hgBound) n x = ⨆ k, a n k := by
    intro n
    exact tendsto_nhds_unique
      (A.tendsto_analyticCubeResolvent_comp mu lam hf hf0 hD hfD n x)
      (tendsto_atTop_ciSup (haMonoRight n) (haBdd n))
  have hleft := A.tendsto_analyticCubeResolvent lam
    (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal hg0 hC hgBound x
  have hleftSup :
      (A.analyticMinimalResolvent lam g
        (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal
        (hgBound) x).toReal = ⨆ n, A.analyticCubeResolvent lam g
          (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal
          (hgBound) n x := by
    apply tendsto_nhds_unique hleft
    exact tendsto_atTop_ciSup
      (A.monotone_analyticCubeResolvent lam
        (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal
        hg0 hgBound x)
      (by
        refine ⟨C / (lam : ℝ), ?_⟩
        rintro y ⟨n, rfl⟩
        exact (le_abs_self _).trans
          (A.abs_analyticCubeResolvent_le lam
            (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal
            hC hgBound n x))
  rw [hleftSup]
  simp_rw [hrow]
  change (⨆ n, ⨆ k, a n k) = ⨆ n, a n n
  have hdiagBdd : BddAbove (Set.range fun n ↦ a n n) := by
    refine ⟨C / (lam : ℝ), ?_⟩
    rintro y ⟨n, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticCubeResolvent_le lam
        (A.measurable_analyticCubeResolvent mu hf hfD n) hC
        (hgkBound n) n x)
  have hrowsBdd : BddAbove (Set.range fun n ↦ ⨆ k, a n k) := by
    refine ⟨C / (lam : ℝ), ?_⟩
    rintro y ⟨n, rfl⟩
    exact ciSup_le fun k ↦ (le_abs_self _).trans
      (A.abs_analyticCubeResolvent_le lam
        (A.measurable_analyticCubeResolvent mu hf hfD k) hC
        (hgkBound k) n x)
  apply le_antisymm
  · refine ciSup_le fun n ↦ ciSup_le fun k ↦ ?_
    exact le_ciSup_of_le hdiagBdd (max n k)
      ((haMonoLeft k (le_max_left n k)).trans
        (haMonoRight (max n k) (le_max_right n k)))
  · refine ciSup_le fun n ↦ ?_
    exact le_ciSup_of_le hrowsBdd n (le_ciSup (haBdd n) n)

/-- The real values of the nonnegative analytic minimal resolvent satisfy the
resolvent equation. -/
theorem analyticMinimalResolvent_toReal_resolventEquation
    (lam mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    (A.analyticMinimalResolvent lam f hf hfD x).toReal =
      (A.analyticMinimalResolvent mu f hf hfD x).toReal +
        ((mu : ℝ) - (lam : ℝ)) *
          (A.analyticMinimalResolvent lam
            (fun y ↦ (A.analyticMinimalResolvent mu f hf hfD y).toReal)
            (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal
            (D := D / (mu : ℝ)) (fun y ↦ by
              rw [abs_of_nonneg ENNReal.toReal_nonneg]
              exact ENNReal.toReal_le_of_le_ofReal
                (div_nonneg hD mu.property.le)
                (A.analyticMinimalResolvent_le mu hf hf0 hD hfD y)) x).toReal := by
  let gk : ℕ → Vec d → ℝ := fun n ↦
    A.analyticCubeResolvent mu f hf hfD n
  let C : ℝ := D / (mu : ℝ)
  have hC : 0 ≤ C := div_nonneg hD mu.property.le
  have hgk0 : ∀ n y, 0 ≤ gk n y := fun n y ↦
    A.analyticCubeResolvent_nonneg mu hf hf0 hfD n y
  have hgkBound : ∀ n y, |gk n y| ≤ C := fun n y ↦
    A.abs_analyticCubeResolvent_le mu hf hD hfD n y
  let c : ℕ → ℝ := fun n ↦ A.analyticCubeResolvent lam (gk n)
    (A.measurable_analyticCubeResolvent mu hf hfD n) (hgkBound n) n x
  have hgkMono : Monotone gk := by
    intro i j hij y
    exact A.monotone_analyticCubeResolvent mu hf hf0 hfD y hij
  have hcMono : Monotone c := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    exact (A.monotone_analyticCubeResolvent lam
      (A.measurable_analyticCubeResolvent mu hf hfD n) (hgk0 n)
      (hgkBound n) x (Nat.le_succ n)).trans
      (A.analyticCubeResolvent_mono lam
        (A.measurable_analyticCubeResolvent mu hf hfD n)
        (A.measurable_analyticCubeResolvent mu hf hfD (n + 1))
        (hgkBound n) (hgkBound (n + 1))
        (hgkMono (Nat.le_succ n)) (n + 1) x)
  have hcBdd : BddAbove (Set.range c) := by
    refine ⟨C / (lam : ℝ), ?_⟩
    rintro y ⟨n, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticCubeResolvent_le lam
        (A.measurable_analyticCubeResolvent mu hf hfD n) hC
        (hgkBound n) n x)
  have hcTendsto : Tendsto c atTop (nhds
      (A.analyticMinimalResolvent lam
        (fun y ↦ (A.analyticMinimalResolvent mu f hf hfD y).toReal)
        (A.measurable_analyticMinimalResolvent mu hf hfD).ennreal_toReal
        (D := C) (fun y ↦ by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_le_of_le_ofReal hC
            (A.analyticMinimalResolvent_le mu hf hf0 hD hfD y)) x).toReal) := by
    rw [A.analyticMinimalResolvent_comp_eq_iSup lam mu hf hf0 hD hfD x]
    exact tendsto_atTop_ciSup hcMono hcBdd
  have hconst : Tendsto (fun _ : ℕ ↦ (mu : ℝ) - (lam : ℝ)) atTop
      (nhds ((mu : ℝ) - (lam : ℝ))) := tendsto_const_nhds
  have hright := (A.tendsto_analyticCubeResolvent mu hf hf0 hD hfD x).add
    (hconst.mul hcTendsto)
  apply tendsto_nhds_unique (A.tendsto_analyticCubeResolvent lam hf hf0 hD hfD x)
  apply hright.congr'
  filter_upwards with n
  exact A.analyticCubeResolvent_resolventEquation lam mu hf hD hfD n x |>.symm

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
