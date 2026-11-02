/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PotentialResolventIdentitiesReg
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PenalizationEverywhere
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PenalizedMinimal
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ResolventIdentity

/-!
# PenalizedIdentities

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Local identities for the whole-space penalized exhaustion

The algebraic resolvent and perturbation identities are first proved on one
exhaustion cube.  They use only the continuous-coefficient representative;
small contrast is not part of these identities.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- The potential load of a local exterior-penalized resolvent. -/
def analyticPenalizedCubeLoad {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) : ℝ :=
  wholeSpacePenalizationPotential V n x *
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x

/-- The potential load of the minimal whole-space exterior-penalized
resolvent. -/
def analyticPenalizedLoad {V : Set (Vec d)} (hV : IsOpen V)
    (n : ℕ) (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (x : Vec d) : ℝ :=
  wholeSpacePenalizationPotential V n x *
    (A.analyticPenalizedResolvent hV n mu f hf hfD x).toReal

theorem measurable_analyticPenalizedCubeLoad {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    Measurable (A.analyticPenalizedCubeLoad hV n mu f hf hfD m) :=
  (measurable_wholeSpacePenalizationPotential hV n).mul
    (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)

/-- The whole-space penalized load is measurable. -/
theorem measurable_analyticPenalizedLoad {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    Measurable (A.analyticPenalizedLoad hV n mu f hf hfD) :=
  (measurable_wholeSpacePenalizationPotential hV n).mul
    (A.measurable_analyticPenalizedResolvent hV n mu hf hfD).ennreal_toReal

/-- A local penalized load is nonnegative for nonnegative data. -/
theorem analyticPenalizedCubeLoad_nonneg {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    0 ≤ A.analyticPenalizedCubeLoad hV n mu f hf hfD m x :=
  mul_nonneg (wholeSpacePenalizationPotential_nonneg V n x)
    (A.analyticPenalizedCubeResolvent_nonneg hV n mu hf hf0 hfD m x)

theorem abs_analyticPenalizedCubeLoad_le {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    |A.analyticPenalizedCubeLoad hV n mu f hf hfD m x| ≤
      n * (D / (mu : ℝ)) := by
  rw [analyticPenalizedCubeLoad, abs_mul,
    abs_of_nonneg (wholeSpacePenalizationPotential_nonneg V n x)]
  exact mul_le_mul
    (wholeSpacePenalizationPotential_le V n x)
    (A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m x)
    (abs_nonneg _) (Nat.cast_nonneg n)

/-- The whole-space penalized load is nonnegative. -/
theorem analyticPenalizedLoad_nonneg {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D)
    (x : Vec d) : 0 ≤ A.analyticPenalizedLoad hV n mu f hf hfD x :=
  mul_nonneg (wholeSpacePenalizationPotential_nonneg V n x)
    ENNReal.toReal_nonneg

/-- The whole-space penalized load has the product of the potential bound
and the resolvent maximum-principle bound as a uniform bound. -/
theorem abs_analyticPenalizedLoad_le {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    |A.analyticPenalizedLoad hV n mu f hf hfD x| ≤
      n * (D / (mu : ℝ)) := by
  rw [abs_of_nonneg (A.analyticPenalizedLoad_nonneg hV n mu hf hfD x),
    analyticPenalizedLoad]
  have hres :
      (A.analyticPenalizedResolvent hV n mu f hf hfD x).toReal ≤
        D / (mu : ℝ) :=
    ENNReal.toReal_le_of_le_ofReal (div_nonneg hD mu.property.le)
      (A.analyticPenalizedResolvent_le hV n mu hf hf0 hD hfD x)
  exact mul_le_mul (wholeSpacePenalizationPotential_le V n x) hres
    ENNReal.toReal_nonneg (Nat.cast_nonneg n)

/-- A fixed outer cube resolvent commutes with the increasing exhaustion
limit in the penalized load. -/
private theorem tendsto_analyticCubeResolvent_penalizedLoad
    {V : Set (Vec d)} (hV : IsOpen V) (n : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D)
    (outer : ℕ) (x : Vec d) :
    Tendsto (fun k ↦ A.analyticCubeResolvent mu
        (A.analyticPenalizedCubeLoad hV n mu f hf hfD k)
        (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD k)
        (A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD k)
        outer x) atTop
      (nhds (A.analyticCubeResolvent mu
        (A.analyticPenalizedLoad hV n mu f hf hfD)
        (A.measurable_analyticPenalizedLoad hV n mu hf hfD)
        (A.abs_analyticPenalizedLoad_le hV n mu hf hf0 hD hfD)
        outer x)) := by
  by_cases hx : x ∈ wholeSpaceCube d outer
  · let hU := isOpenBoundedConvexDomain_wholeSpaceCube d outer
    let gk : ℕ → Vec d → ℝ := fun k ↦
      A.analyticPenalizedCubeLoad hV n mu f hf hfD k
    let g : Vec d → ℝ := A.analyticPenalizedLoad hV n mu f hf hfD
    let C : ℝ := n * (D / (mu : ℝ))
    have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg n)
      (div_nonneg hD mu.property.le)
    have hgkBound : ∀ k y, |gk k y| ≤ C := fun k y ↦
      A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD k y
    have hgBound : ∀ y, |g y| ≤ C := fun y ↦
      A.abs_analyticPenalizedLoad_le hV n mu hf hf0 hD hfD y
    let Fk : ℕ → ScalarL2 (wholeSpaceCube d outer) := fun k ↦
      boundedMeasurableToScalarL2 hU
        ((A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD k).comp
          measurable_subtype_coe) (fun y ↦ hgkBound k y)
    let Fl : ScalarL2 (wholeSpaceCube d outer) :=
      boundedMeasurableToScalarL2 hU
        ((A.measurable_analyticPenalizedLoad hV n mu hf hfD).comp
          measurable_subtype_coe) (fun y ↦ hgBound y)
    have hpt : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d outer),
        Tendsto (fun k ↦ Fk k y) atTop (nhds (Fl y)) := by
      have hFk : ∀ k, Fk k =ᵐ[volumeMeasureOn (wholeSpaceCube d outer)]
          domainExtension (gk k ∘ Subtype.val) := fun k ↦
        boundedMeasurableToScalarL2_coeFn hU
          ((A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD k).comp
            measurable_subtype_coe) (fun y ↦ hgkBound k y)
      have hFl := boundedMeasurableToScalarL2_coeFn hU
        ((A.measurable_analyticPenalizedLoad hV n mu hf hfD).comp
          measurable_subtype_coe) (fun y ↦ hgBound y)
      filter_upwards [ae_all_iff.2 hFk, hFl,
        ae_restrict_mem hU.isOpen.measurableSet] with y hyk hyl hyU
      rw [hyl, domainExtension_of_mem hyU]
      have ht := A.tendsto_analyticPenalizedCubeResolvent hV n mu hf hf0 hD hfD y
      have hmul : Tendsto (fun k : ℕ ↦
          wholeSpacePenalizationPotential V n y *
            A.analyticPenalizedCubeResolvent hV n mu f hf hfD k y) atTop
          (nhds (wholeSpacePenalizationPotential V n y *
            (A.analyticPenalizedResolvent hV n mu f hf hfD y).toReal)) :=
        tendsto_const_nhds.mul ht
      apply hmul.congr'
      filter_upwards with k
      rw [hyk k, domainExtension_of_mem hyU]
      rfl
    have hdiff : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d outer),
        ∀ k, |Fk k y - Fl y| ≤ 2 * C := by
      have hFk : ∀ k, Fk k =ᵐ[volumeMeasureOn (wholeSpaceCube d outer)]
          domainExtension (gk k ∘ Subtype.val) := fun k ↦
        boundedMeasurableToScalarL2_coeFn hU
          ((A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD k).comp
            measurable_subtype_coe) (fun y ↦ hgkBound k y)
      have hFl := boundedMeasurableToScalarL2_coeFn hU
        ((A.measurable_analyticPenalizedLoad hV n mu hf hfD).comp
          measurable_subtype_coe) (fun y ↦ hgBound y)
      filter_upwards [ae_all_iff.2 hFk, hFl,
        ae_restrict_mem hU.isOpen.measurableSet] with y hyk hyl hyU
      intro k
      rw [hyk k, hyl, domainExtension_of_mem hyU,
        domainExtension_of_mem hyU]
      calc
        |gk k y - g y| ≤ |gk k y| + |g y| := abs_sub _ _
        _ ≤ C + C := add_le_add (hgkBound k y) (hgBound y)
        _ = 2 * C := by ring
    have hnorm : Tendsto (fun k ↦ ‖Fk k - Fl‖) atTop (nhds 0) :=
      tendsto_norm_scalarL2_sub_of_bounded_ae_tendsto hU hdiff hpt
    have hdiff' : ∀ k, ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d outer),
        |Fk k y - Fl y| ≤ 2 * C := fun k ↦ hdiff.mono fun _ hy ↦ hy k
    exact tendsto_representative_of_tendsto_norm_continuousCoeff A.a hU
      mu.property A.hnu (A.cubeEllipticity outer) A.hsymm
      (A.skewContinuousOnCube outer) A.hd
      (M := 2 * C) (mul_nonneg (by norm_num) hC) hdiff' hnorm
      (fun k ↦ A.continuousOn_analyticCubeResolvent mu
        (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD k)
        (A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD k) outer)
      (fun k ↦ A.analyticCubeResolvent_ae mu
        (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD k)
        (A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD k) outer)
      (A.continuousOn_analyticCubeResolvent mu
        (A.measurable_analyticPenalizedLoad hV n mu hf hfD)
        (A.abs_analyticPenalizedLoad_le hV n mu hf hf0 hD hfD) outer)
      (A.analyticCubeResolvent_ae mu
        (A.measurable_analyticPenalizedLoad hV n mu hf hfD)
        (A.abs_analyticPenalizedLoad_le hV n mu hf hf0 hD hfD) outer) hx
  · simp only [analyticCubeResolvent, dite_eq_right hx]
    exact tendsto_const_nhds

/-- The diagonal of the domain exhaustion and the increasing penalized-load
approximation computes the minimal resolvent of the whole-space load. -/
private theorem analyticMinimalResolvent_penalizedLoad_eq_iSup
    {V : Set (Vec d)} (hV : IsOpen V) (n : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    (A.analyticMinimalResolvent mu
      (A.analyticPenalizedLoad hV n mu f hf hfD)
      (A.measurable_analyticPenalizedLoad hV n mu hf hfD)
      (A.abs_analyticPenalizedLoad_le hV n mu hf hf0 hD hfD) x).toReal =
      ⨆ m, A.analyticCubeResolvent mu
        (A.analyticPenalizedCubeLoad hV n mu f hf hfD m)
        (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m)
        (A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD m) m x := by
  let gk : ℕ → Vec d → ℝ := fun k ↦
    A.analyticPenalizedCubeLoad hV n mu f hf hfD k
  let g : Vec d → ℝ := A.analyticPenalizedLoad hV n mu f hf hfD
  let C : ℝ := n * (D / (mu : ℝ))
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg n)
    (div_nonneg hD mu.property.le)
  have hgk0 : ∀ k y, 0 ≤ gk k y := fun k y ↦
    A.analyticPenalizedCubeLoad_nonneg hV n mu hf hf0 hfD k y
  have hg0 : ∀ y, 0 ≤ g y := fun y ↦
    A.analyticPenalizedLoad_nonneg hV n mu hf hfD y
  have hgkBound : ∀ k y, |gk k y| ≤ C := fun k y ↦
    A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD k y
  have hgBound : ∀ y, |g y| ≤ C := fun y ↦
    A.abs_analyticPenalizedLoad_le hV n mu hf hf0 hD hfD y
  let a : ℕ → ℕ → ℝ := fun outer k ↦
    A.analyticCubeResolvent mu (gk k)
      (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD k)
      (hgkBound k) outer x
  have haMonoLeft : ∀ k, Monotone fun outer ↦ a outer k := by
    intro k
    exact A.monotone_analyticCubeResolvent mu
      (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD k)
      (hgk0 k) (hgkBound k) x
  have hgkMono : Monotone gk := by
    intro i j hij y
    exact mul_le_mul_of_nonneg_left
      (A.monotone_analyticPenalizedCubeResolvent hV n mu hf hf0 hfD y hij)
      (wholeSpacePenalizationPotential_nonneg V n y)
  have haMonoRight : ∀ outer, Monotone (a outer) := by
    intro outer i j hij
    exact A.analyticCubeResolvent_mono mu
      (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD i)
      (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD j)
      (hgkBound i) (hgkBound j) (hgkMono hij) outer x
  have haBdd : ∀ outer, BddAbove (Set.range (a outer)) := by
    intro outer
    refine ⟨C / (mu : ℝ), ?_⟩
    rintro y ⟨k, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticCubeResolvent_le mu
        (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD k)
        hC (hgkBound k) outer x)
  have hrow : ∀ outer,
      A.analyticCubeResolvent mu g
          (A.measurable_analyticPenalizedLoad hV n mu hf hfD)
          hgBound outer x = ⨆ k, a outer k := by
    intro outer
    exact tendsto_nhds_unique
      (A.tendsto_analyticCubeResolvent_penalizedLoad hV n mu hf hf0 hD hfD
        outer x)
      (tendsto_atTop_ciSup (haMonoRight outer) (haBdd outer))
  have hleft := A.tendsto_analyticCubeResolvent mu
    (A.measurable_analyticPenalizedLoad hV n mu hf hfD) hg0 hC hgBound x
  have hleftSup :
      (A.analyticMinimalResolvent mu g
        (A.measurable_analyticPenalizedLoad hV n mu hf hfD)
        hgBound x).toReal = ⨆ outer,
          A.analyticCubeResolvent mu g
            (A.measurable_analyticPenalizedLoad hV n mu hf hfD)
            hgBound outer x := by
    apply tendsto_nhds_unique hleft
    exact tendsto_atTop_ciSup
      (A.monotone_analyticCubeResolvent mu
        (A.measurable_analyticPenalizedLoad hV n mu hf hfD) hg0 hgBound x)
      (by
        refine ⟨C / (mu : ℝ), ?_⟩
        rintro y ⟨outer, rfl⟩
        exact (le_abs_self _).trans
          (A.abs_analyticCubeResolvent_le mu
            (A.measurable_analyticPenalizedLoad hV n mu hf hfD)
            hC hgBound outer x))
  change (A.analyticMinimalResolvent mu g
      (A.measurable_analyticPenalizedLoad hV n mu hf hfD) hgBound x).toReal = _
  rw [hleftSup]
  simp_rw [hrow]
  change (⨆ outer, ⨆ k, a outer k) = ⨆ m, a m m
  have hdiagBdd : BddAbove (Set.range fun m ↦ a m m) := by
    refine ⟨C / (mu : ℝ), ?_⟩
    rintro y ⟨m, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticCubeResolvent_le mu
        (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m)
        hC (hgkBound m) m x)
  have hrowsBdd : BddAbove (Set.range fun outer ↦ ⨆ k, a outer k) := by
    refine ⟨C / (mu : ℝ), ?_⟩
    rintro y ⟨outer, rfl⟩
    exact ciSup_le fun k ↦ (le_abs_self _).trans
      (A.abs_analyticCubeResolvent_le mu
        (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD k)
        hC (hgkBound k) outer x)
  apply le_antisymm
  · refine ciSup_le fun outer ↦ ciSup_le fun k ↦ ?_
    exact le_ciSup_of_le hdiagBdd (max outer k)
      ((haMonoLeft k (le_max_left outer k)).trans
        (haMonoRight (max outer k) (le_max_right outer k)))
  · refine ciSup_le fun m ↦ ?_
    exact le_ciSup_of_le hrowsBdd m (le_ciSup (haBdd m) m)

private theorem boundedMeasurableToScalarL2_penalizedLoad {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        ((A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m).comp
          measurable_subtype_coe)
        (fun y ↦ A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD m y) =
      potentialMul (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m)
        (potentialResolvent A.a mu.property A.hnu
          (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
          (wholeSpacePenalizationPotential_isBounded hV n m)
          (boundedMeasurableToScalarL2
            (isOpenBoundedConvexDomain_wholeSpaceCube d m)
            (hf.comp measurable_subtype_coe) (fun y ↦ hfD y))) := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  refine (Lp.ext_iff).2 ?_
  filter_upwards [boundedMeasurableToScalarL2_coeFn hU
      ((A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m).comp
        measurable_subtype_coe)
      (fun y ↦ A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD m y),
    potentialMul_coeFn (U := wholeSpaceCube d m)
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m)
      (potentialResolvent A.a mu.property A.hnu
        (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m)
        (boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
          (fun y ↦ hfD y))),
    A.analyticPenalizedCubeResolvent_ae hV n mu hf hfD m,
    ae_restrict_mem hU.isOpen.measurableSet] with x hload hmul hrep hx
  rw [hload, domainExtension_of_mem hx, hmul]
  change wholeSpacePenalizationPotential V n x *
      A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x = _
  rw [hrep]

/-- The subtraction-free perturbation identity on one exhaustion cube. -/
theorem analyticPenalizedCubeResolvent_perturbation {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift) {f : Vec d → ℝ}
    (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x +
        A.analyticCubeResolvent mu
          (A.analyticPenalizedCubeLoad hV n mu f hf hfD m)
          (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m)
          (A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD m) m x =
      A.analyticCubeResolvent mu f hf hfD m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
    let F : ScalarL2 (wholeSpaceCube d m) :=
      boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
        (fun y ↦ hfD y)
    have hid := potentialResolvent_perturbation_identity A.a mu.property
      A.hnu (A.cubeEllipticity m)
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m) F
    have hload := boundedMeasurableToScalarL2_penalizedLoad A hV n mu hf hD hfD m
    have haeP := A.analyticPenalizedCubeResolvent_ae hV n mu hf hfD m
    have haeL := A.analyticCubeResolvent_ae mu
      (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m)
      (A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD m) m
    rw [hload] at haeL
    have haeF := A.analyticCubeResolvent_ae mu hf hfD m
    have hae : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m),
        A.analyticPenalizedCubeResolvent hV n mu f hf hfD m y +
            A.analyticCubeResolvent mu
              (A.analyticPenalizedCubeLoad hV n mu f hf hfD m)
              (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m)
              (A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD m) m y =
          A.analyticCubeResolvent mu f hf hfD m y := by
      filter_upwards [haeP, haeL, haeF,
        Lp.coeFn_sub
          (alphaShiftedResolvent A.a mu.property A.hnu
            (A.cubeEllipticity m) F)
          (alphaShiftedResolvent A.a mu.property A.hnu
            (A.cubeEllipticity m)
            (potentialMul (wholeSpacePenalizationPotential V n)
              (wholeSpacePenalizationPotential_isBounded hV n m)
              (potentialResolvent A.a mu.property A.hnu
                (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
                (wholeSpacePenalizationPotential_isBounded hV n m) F)))]
          with y hp hl hf hsub
      have hidy := congrArg (fun w : ScalarL2 (wholeSpaceCube d m) ↦ w y) hid
      have hidy' :
          (potentialResolvent A.a mu.property A.hnu
              (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
              (wholeSpacePenalizationPotential_isBounded hV n m) F) y =
            (alphaShiftedResolvent A.a mu.property A.hnu
                (A.cubeEllipticity m) F) y -
              (alphaShiftedResolvent A.a mu.property A.hnu
                (A.cubeEllipticity m)
                (potentialMul (wholeSpacePenalizationPotential V n)
                  (wholeSpacePenalizationPotential_isBounded hV n m)
                  (potentialResolvent A.a mu.property A.hnu
                    (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
                    (wholeSpacePenalizationPotential_isBounded hV n m) F))) y := by
        simpa only [hsub, Pi.sub_apply] using hidy
      rw [hp, hl, hf]
      linarith only [hidy']
    exact eqOn_of_continuousOn_of_ae_eq hU.isOpen
      ((A.continuousOn_analyticPenalizedCubeResolvent hV n mu hf hfD m).add
        (A.continuousOn_analyticCubeResolvent mu
          (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m)
          (A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD m) m))
      (A.continuousOn_analyticCubeResolvent mu hf hfD m) hae hx
  · rw [analyticPenalizedCubeResolvent, dite_eq_right hx,
      analyticCubeResolvent, dite_eq_right hx, analyticCubeResolvent, dite_eq_right hx,
      zero_add]

/-- The subtraction-free perturbation identity passes to the whole-space
exhaustion for nonnegative bounded data. -/
theorem analyticPenalizedResolvent_perturbation {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hD : 0 ≤ D) (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    (A.analyticPenalizedResolvent hV n mu f hf hfD x).toReal +
        (A.analyticMinimalResolvent mu
          (A.analyticPenalizedLoad hV n mu f hf hfD)
          (A.measurable_analyticPenalizedLoad hV n mu hf hfD)
          (A.abs_analyticPenalizedLoad_le hV n mu hf hf0 hD hfD) x).toReal =
      (A.analyticMinimalResolvent mu f hf hfD x).toReal := by
  let gk : ℕ → Vec d → ℝ := fun k ↦
    A.analyticPenalizedCubeLoad hV n mu f hf hfD k
  let C : ℝ := n * (D / (mu : ℝ))
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg n)
    (div_nonneg hD mu.property.le)
  have hgk0 : ∀ k y, 0 ≤ gk k y := fun k y ↦
    A.analyticPenalizedCubeLoad_nonneg hV n mu hf hf0 hfD k y
  have hgkBound : ∀ k y, |gk k y| ≤ C := fun k y ↦
    A.abs_analyticPenalizedCubeLoad_le hV n mu hf hD hfD k y
  let c : ℕ → ℝ := fun m ↦
    A.analyticCubeResolvent mu (gk m)
      (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m)
      (hgkBound m) m x
  have hgkMono : Monotone gk := by
    intro i j hij y
    exact mul_le_mul_of_nonneg_left
      (A.monotone_analyticPenalizedCubeResolvent hV n mu hf hf0 hfD y hij)
      (wholeSpacePenalizationPotential_nonneg V n y)
  have hcMono : Monotone c := by
    refine monotone_nat_of_le_succ fun m ↦ ?_
    exact (A.monotone_analyticCubeResolvent mu
      (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m)
      (hgk0 m) (hgkBound m) x (Nat.le_succ m)).trans
      (A.analyticCubeResolvent_mono mu
        (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m)
        (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD (m + 1))
        (hgkBound m) (hgkBound (m + 1))
        (hgkMono (Nat.le_succ m)) (m + 1) x)
  have hcBdd : BddAbove (Set.range c) := by
    refine ⟨C / (mu : ℝ), ?_⟩
    rintro y ⟨m, rfl⟩
    exact (le_abs_self _).trans
      (A.abs_analyticCubeResolvent_le mu
        (A.measurable_analyticPenalizedCubeLoad hV n mu hf hfD m)
        hC (hgkBound m) m x)
  have hcTendsto : Tendsto c atTop (nhds
      (A.analyticMinimalResolvent mu
        (A.analyticPenalizedLoad hV n mu f hf hfD)
        (A.measurable_analyticPenalizedLoad hV n mu hf hfD)
        (A.abs_analyticPenalizedLoad_le hV n mu hf hf0 hD hfD) x).toReal) := by
    rw [A.analyticMinimalResolvent_penalizedLoad_eq_iSup hV n mu hf hf0 hD hfD x]
    exact tendsto_atTop_ciSup hcMono hcBdd
  have hleft :=
    (A.tendsto_analyticPenalizedCubeResolvent hV n mu hf hf0 hD hfD x).add
      hcTendsto
  apply tendsto_nhds_unique hleft
  apply (A.tendsto_analyticCubeResolvent mu hf hf0 hD hfD x).congr'
  filter_upwards with m
  exact A.analyticPenalizedCubeResolvent_perturbation hV n mu hf hD hfD m x |>.symm

private theorem boundedMeasurableToScalarL2_penalizedCubeResolvent
    {V : Set (Vec d)} (hV : IsOpen V) (n : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) :
    boundedMeasurableToScalarL2
        (isOpenBoundedConvexDomain_wholeSpaceCube d m)
        ((A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m).comp
          measurable_subtype_coe)
        (fun y ↦ A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m y) =
      potentialResolvent A.a mu.property A.hnu
        (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
        (wholeSpacePenalizationPotential_isBounded hV n m)
        (boundedMeasurableToScalarL2
          (isOpenBoundedConvexDomain_wholeSpaceCube d m)
          (hf.comp measurable_subtype_coe) (fun y ↦ hfD y)) := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  refine (Lp.ext_iff).2 ?_
  filter_upwards [boundedMeasurableToScalarL2_coeFn hU
      ((A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m).comp
        measurable_subtype_coe)
      (fun y ↦ A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m y),
    A.analyticPenalizedCubeResolvent_ae hV n mu hf hfD m,
    ae_restrict_mem hU.isOpen.measurableSet] with x hbounded hrep hx
  rw [hbounded, domainExtension_of_mem hx]
  simpa only [Function.comp_apply] using hrep

/-- The resolvent identity for a fixed exterior penalty on one exhaustion
cube. -/
theorem analyticPenalizedCubeResolvent_resolventIdentity {V : Set (Vec d)}
    (hV : IsOpen V) (n : ℕ) (mu nu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    A.analyticPenalizedCubeResolvent hV n mu f hf hfD m x =
      A.analyticPenalizedCubeResolvent hV n nu f hf hfD m x +
        ((nu : ℝ) - (mu : ℝ)) *
          A.analyticPenalizedCubeResolvent hV n nu
            (A.analyticPenalizedCubeResolvent hV n mu f hf hfD m)
            (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)
            (A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m) m x := by
  by_cases hx : x ∈ wholeSpaceCube d m
  · let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
    let F : ScalarL2 (wholeSpaceCube d m) :=
      boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
        (fun y ↦ hfD y)
    have hid := potentialResolvent_resolvent_identity_apply A.a
      A.hnu (A.cubeEllipticity m)
      (wholeSpacePenalizationPotential V n)
      (wholeSpacePenalizationPotential_isBounded hV n m) mu nu F
    have hinner := boundedMeasurableToScalarL2_penalizedCubeResolvent A hV n mu
      hf hD hfD m
    have haeMu := A.analyticPenalizedCubeResolvent_ae hV n mu hf hfD m
    have haeNu := A.analyticPenalizedCubeResolvent_ae hV n nu hf hfD m
    have haeComp := A.analyticPenalizedCubeResolvent_ae hV n nu
      (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)
      (A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m) m
    rw [hinner] at haeComp
    have hae : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m),
        A.analyticPenalizedCubeResolvent hV n mu f hf hfD m y =
          A.analyticPenalizedCubeResolvent hV n nu f hf hfD m y +
            ((nu : ℝ) - (mu : ℝ)) *
              A.analyticPenalizedCubeResolvent hV n nu
                (A.analyticPenalizedCubeResolvent hV n mu f hf hfD m)
                (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)
                (A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m)
                m y := by
      filter_upwards [haeMu, haeNu, haeComp,
        Lp.coeFn_add
          (potentialResolvent A.a nu.property A.hnu
            (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
            (wholeSpacePenalizationPotential_isBounded hV n m) F)
          (((nu : ℝ) - (mu : ℝ)) •
            potentialResolvent A.a nu.property A.hnu
              (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
              (wholeSpacePenalizationPotential_isBounded hV n m)
              (potentialResolvent A.a mu.property A.hnu
                (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
                (wholeSpacePenalizationPotential_isBounded hV n m) F)),
        Lp.coeFn_smul ((nu : ℝ) - (mu : ℝ))
          (potentialResolvent A.a nu.property A.hnu
            (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
            (wholeSpacePenalizationPotential_isBounded hV n m)
            (potentialResolvent A.a mu.property A.hnu
              (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
              (wholeSpacePenalizationPotential_isBounded hV n m) F))]
          with y hmu hnu hcomp hadd hsmul
      have hidy := congrArg (fun w : ScalarL2 (wholeSpaceCube d m) ↦ w y) hid
      have hidy' :
          (potentialResolvent A.a mu.property A.hnu
              (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
              (wholeSpacePenalizationPotential_isBounded hV n m) F) y =
            (potentialResolvent A.a nu.property A.hnu
                (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
                (wholeSpacePenalizationPotential_isBounded hV n m) F) y +
              ((nu : ℝ) - (mu : ℝ)) *
                (potentialResolvent A.a nu.property A.hnu
                  (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
                  (wholeSpacePenalizationPotential_isBounded hV n m)
                  (potentialResolvent A.a mu.property A.hnu
                    (A.cubeEllipticity m) (wholeSpacePenalizationPotential V n)
                    (wholeSpacePenalizationPotential_isBounded hV n m) F)) y := by
        simpa only [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul] using hidy
      simpa only [hmu, hnu, hcomp] using hidy'
    exact eqOn_of_continuousOn_of_ae_eq hU.isOpen
      (A.continuousOn_analyticPenalizedCubeResolvent hV n mu hf hfD m)
      ((A.continuousOn_analyticPenalizedCubeResolvent hV n nu hf hfD m).add
        (continuousOn_const.mul
          (A.continuousOn_analyticPenalizedCubeResolvent hV n nu
            (A.measurable_analyticPenalizedCubeResolvent hV n mu hf hfD m)
            (A.abs_analyticPenalizedCubeResolvent_le hV n mu hf hD hfD m) m)))
      hae hx
  · rw [analyticPenalizedCubeResolvent, dite_eq_right hx,
      analyticPenalizedCubeResolvent, dite_eq_right hx,
      analyticPenalizedCubeResolvent, dite_eq_right hx, mul_zero, add_zero]

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
