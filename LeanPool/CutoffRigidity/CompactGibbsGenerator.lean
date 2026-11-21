/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.ClassicalEigenspace
public import LeanPool.CutoffRigidity.GibbsStationarity
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# A genuine densely defined closable Gibbs L² generator

The operator acts on actual L² classes admitting compact C² representatives.
Full support makes its representative and differential output well defined.
Smooth compact approximation gives density; actual Gibbs integration by parts
proves symmetry and dissipativity, hence closability. Essential self-adjointness,
spectral compactness and gap attainment are not asserted here.
-/

public section

namespace CutoffRigidity

open MeasureTheory
open scoped LinearPMap
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Genuine L² classes represented by compact C² functions. -/
@[expose] noncomputable def compactGibbsGeneratorDomain (V : E → ℝ) :
    Submodule ℝ (E →₂[gibbsMeasure volume V] ℝ) where
  carrier := {u | ∃ f : E → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
    f =ᵐ[gibbsMeasure volume V] u}
  zero_mem' := ⟨fun _ => 0, contDiff_const, by simp [HasCompactSupport], (Lp.coeFn_zero _ _ _).symm⟩
  add_mem' := by
    rintro u v ⟨f, hf, hfc, haef⟩ ⟨g, hg, hgc, haeg⟩
    refine ⟨fun x => f x + g x, hf.add hg, ?_, ?_⟩
    · simpa only [Pi.add_def] using hfc.add hgc
    · filter_upwards [haef, haeg, Lp.coeFn_add u v] with x hx hy hxy
      simpa only [Pi.add_apply] using (hx ▸ hy ▸ hxy.symm)
  smul_mem' := by
    rintro r u ⟨f, hf, hfc, haef⟩
    refine ⟨fun x => r * f x, contDiff_const.mul hf, ?_, ?_⟩
    · exact hfc.comp_left (g := fun t : ℝ => r * t) (by simp)
    · filter_upwards [haef, Lp.coeFn_smul r u] with x hx hxy
      simpa only [Pi.smul_apply, smul_eq_mul] using (hx ▸ hxy.symm)

/-- The unique continuous compact representative, chosen from the actual domain. -/
@[expose] noncomputable def compactGibbsRepresentative (V : E → ℝ)
    (u : compactGibbsGeneratorDomain V) : E → ℝ := Classical.choose u.property

theorem compactGibbsRepresentative_spec (V : E → ℝ) (u : compactGibbsGeneratorDomain V) :
    ContDiff ℝ 2 (compactGibbsRepresentative V u) ∧ HasCompactSupport (compactGibbsRepresentative V
      u) ∧
      compactGibbsRepresentative V u =ᵐ[gibbsMeasure volume V] (u : E →₂[gibbsMeasure volume V] ℝ)
        :=
  Classical.choose_spec u.property

/-- The representative is unique everywhere, rather than only almost everywhere. -/
theorem compactGibbsRepresentative_unique {V f : E → ℝ} (hV : Continuous V)
    (u : compactGibbsGeneratorDomain V) (hf : Continuous f)
    (hae : f =ᵐ[gibbsMeasure volume V] (u : E →₂[gibbsMeasure volume V] ℝ)) :
    f = compactGibbsRepresentative V u :=
  gibbsMeasure_eq_of_ae_eq volume hV.measurable hf (compactGibbsRepresentative_spec V
    u).1.continuous
    (hae.trans (compactGibbsRepresentative_spec V u).2.2.symm)

/-- Canonical compact representatives depend linearly on their actual L² classes. -/
@[expose] noncomputable def compactGibbsRepresentativeLinear (V : E → ℝ) (hV : Continuous V) :
    compactGibbsGeneratorDomain V →ₗ[ℝ] (E → ℝ) where
  toFun := compactGibbsRepresentative V
  map_add' := by
    intro u v
    apply Eq.symm
    apply compactGibbsRepresentative_unique hV (u + v)
    · exact (compactGibbsRepresentative_spec V u).1.continuous.add
        (compactGibbsRepresentative_spec V v).1.continuous
    · filter_upwards [(compactGibbsRepresentative_spec V u).2.2,
        (compactGibbsRepresentative_spec V v).2.2,
        Lp.coeFn_add (u : E →₂[gibbsMeasure volume V] ℝ) v] with x hx hy hxy
      simpa only [Pi.add_apply] using (hx ▸ hy ▸ hxy.symm)
  map_smul' := by
    intro r u
    apply Eq.symm
    apply compactGibbsRepresentative_unique hV (r • u)
    · exact continuous_const.mul (compactGibbsRepresentative_spec V u).1.continuous
    · filter_upwards [(compactGibbsRepresentative_spec V u).2.2,
        Lp.coeFn_smul r (u : E →₂[gibbsMeasure volume V] ℝ)] with x hx hxy
      simpa only [Pi.smul_apply, smul_eq_mul] using (hx ▸ hxy.symm)

/-- The original differential expression is genuinely L² on this compact domain. -/
theorem compactGibbsGenerator_memLp {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : compactGibbsGeneratorDomain V) :
    MemLp (langevinDifferentialOperator V (compactGibbsRepresentative V u)) 2 (gibbsMeasure volume
      V) := by
  let := hprob
  exact Continuous.memLp_of_hasCompactSupport
    (continuous_langevinDifferentialOperator hV (compactGibbsRepresentative_spec V u).1)
    (hasCompactSupport_langevinDifferentialOperator V
      (compactGibbsRepresentative_spec V u).2.1)

/-- Dense domain in the actual Gibbs L² topology, derived from smooth compact approximation. -/
theorem compactGibbsGeneratorDomain_dense (V : E → ℝ)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Dense (compactGibbsGeneratorDomain V : Set (E →₂[gibbsMeasure volume V] ℝ)) := by
  let := hprob
  apply (Lp.dense_hasCompactSupport_contDiff (μ := gibbsMeasure volume V)
    (F := ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono
  rintro u ⟨f, hae, hfc, hf⟩
  exact ⟨f, hf.of_le (by norm_num), hfc, hae.symm⟩

/-- The actual compact-domain differential generator, as a linear map into
Gibbs L² rather than merely a differential expression on functions. -/
@[expose] noncomputable def compactGibbsGeneratorMap {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    compactGibbsGeneratorDomain V →ₗ[ℝ] (E →₂[gibbsMeasure volume V] ℝ) where
  toFun := fun u => (compactGibbsGenerator_memLp hV hprob u).toLp
    (langevinDifferentialOperator V (compactGibbsRepresentative V u))
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [(compactGibbsGenerator_memLp hV hprob (u + v)).coeFn_toLp,
      (compactGibbsGenerator_memLp hV hprob u).coeFn_toLp,
      (compactGibbsGenerator_memLp hV hprob v).coeFn_toLp,
      Lp.coeFn_add ((compactGibbsGenerator_memLp hV hprob u).toLp _)
        ((compactGibbsGenerator_memLp hV hprob v).toLp _)] with x huv hu hv hadd
    rw [huv, hadd, Pi.add_apply, hu, hv]
    have hrep := (compactGibbsRepresentativeLinear V hV.continuous).map_add u v
    change compactGibbsRepresentative V (u + v) = fun x =>
      compactGibbsRepresentative V u x + compactGibbsRepresentative V v x at hrep
    rw [hrep]
    exact langevinDifferentialOperator_add_classical V
      (compactGibbsRepresentative_spec V u).1 (compactGibbsRepresentative_spec V v).1 x
  map_smul' := by
    intro r u
    apply Lp.ext
    filter_upwards [(compactGibbsGenerator_memLp hV hprob (r • u)).coeFn_toLp,
      (compactGibbsGenerator_memLp hV hprob u).coeFn_toLp,
      Lp.coeFn_smul r ((compactGibbsGenerator_memLp hV hprob u).toLp _)] with x hru hu hsmul
    simp only [RingHom.id_apply]
    rw [hru, hsmul, Pi.smul_apply, smul_eq_mul, hu]
    have hrep := (compactGibbsRepresentativeLinear V hV.continuous).map_smul r u
    change compactGibbsRepresentative V (r • u) =
      (fun x => r * compactGibbsRepresentative V u x) at hrep
    rw [hrep]
    exact langevinDifferentialOperator_smul_classical V (compactGibbsRepresentative_spec V u).1 r x

/-- The actual densely defined compact C² Gibbs L² operator. -/
@[expose] noncomputable def compactGibbsGenerator {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (E →₂[gibbsMeasure volume V] ℝ) →ₗ.[ℝ] (E →₂[gibbsMeasure volume V] ℝ) where
  domain := compactGibbsGeneratorDomain V
  toFun := compactGibbsGeneratorMap hV hprob

/-- The L² differential output has the expected actual pointwise representative. -/
theorem compactGibbsGenerator_coeFn {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : compactGibbsGeneratorDomain V) :
    compactGibbsGenerator hV hprob u =ᵐ[gibbsMeasure volume V]
      langevinDifferentialOperator V (compactGibbsRepresentative V u) :=
  (compactGibbsGenerator_memLp hV hprob u).coeFn_toLp

/-- The operator's Hilbert inner product is the actual Gibbs integral. -/
theorem inner_compactGibbsGenerator {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u v : compactGibbsGeneratorDomain V) :
    inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (compactGibbsGenerator hV hprob v) =
      ∫ x, compactGibbsRepresentative V u x *
        langevinDifferentialOperator V (compactGibbsRepresentative V v) x ∂gibbsMeasure volume V
          := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(compactGibbsRepresentative_spec V u).2.2,
    compactGibbsGenerator_coeFn hV hprob v] with x hu hv
  rw [← hu, hv, Real.inner_apply]

/-- Genuine Hilbert-space symmetry of the actual densely defined operator. -/
theorem compactGibbsGenerator_isFormalAdjoint {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (compactGibbsGenerator hV hprob).IsFormalAdjoint (compactGibbsGenerator hV hprob) := by
  intro u v
  rw [real_inner_comm (v : E →₂[gibbsMeasure volume V] ℝ) (compactGibbsGenerator hV hprob u),
    inner_compactGibbsGenerator hV hprob v u, inner_compactGibbsGenerator hV hprob u v]
  exact integral_langevinDifferentialOperator_compact_symmetric hV
    (compactGibbsRepresentative_spec V v).1 (compactGibbsRepresentative_spec V u).1
    (compactGibbsRepresentative_spec V v).2.1 (compactGibbsRepresentative_spec V u).2.1

/-- Genuine dissipativity in the actual Gibbs L² Hilbert space. -/
theorem compactGibbsGenerator_dissipative {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : compactGibbsGeneratorDomain V) :
    inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (compactGibbsGenerator hV hprob u) ≤ 0 := by
  rw [inner_compactGibbsGenerator]
  exact integral_mul_langevinDifferentialOperator_compact_nonpos hV
    (compactGibbsRepresentative_spec V u).1 (compactGibbsRepresentative_spec V u).2.1

/-- Symmetry and the proved dense domain imply genuine operator closability. -/
theorem compactGibbsGenerator_isClosable {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (compactGibbsGenerator hV hprob).IsClosable := by
  have hd : Dense ((compactGibbsGenerator hV hprob).domain : Set (E →₂[gibbsMeasure volume V] ℝ)) :=
    compactGibbsGeneratorDomain_dense V hprob
  have hs := compactGibbsGenerator_isFormalAdjoint hV hprob
  have hle := LinearPMap.IsFormalAdjoint.le_adjoint hd hs
  exact (LinearPMap.adjoint_isClosed hd).isClosable.leIsClosable hle

/-- The resulting graph closure is an actual closed L² operator. -/
theorem compactGibbsGenerator_closure_isClosed {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    (compactGibbsGenerator hV hprob).closure.IsClosed :=
  (compactGibbsGenerator_isClosable hV hprob).closure_isClosed

/-- The actual Green identity allows a noncompact C² first argument when
the other argument is a compact C² test. All products are localized. -/
theorem gibbs_generator_green_one_compact {V f g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    (∫ x, f x * langevinDifferentialOperator V g x ∂gibbsMeasure volume V) =
      ∫ x, g x * langevinDifferentialOperator V f x ∂gibbsMeasure volume V := by
  rw [gibbs_energy_compact_differentiated_test hV hf hg hgc,
    compact_test_gibbs_energy hV (hg.of_le (by norm_num)) hf hgc]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => real_inner_comm _ _))

/-- Classical eigenclasses satisfy the genuine Hilbert adjoint pairing
against every compact-domain test, without global derivative assumptions. -/
theorem classicalEigen_compactGenerator_adjoint_pairing {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ)
    (u : classicalL2Eigenspace V ρ) (v : compactGibbsGeneratorDomain V) :
    inner ℝ ((-ρ) • (u : E →₂[gibbsMeasure volume V] ℝ)) (v : E →₂[gibbsMeasure volume V] ℝ) =
      inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (compactGibbsGenerator hV hprob v) := by
  have hleft : inner ℝ ((-ρ) • (u : E →₂[gibbsMeasure volume V] ℝ))
      (v : E →₂[gibbsMeasure volume V] ℝ) =
      ∫ x, compactGibbsRepresentative V v x * (-ρ * classicalEigenRepresentative V ρ u x)
        ∂gibbsMeasure volume V := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul (-ρ) (u : E →₂[gibbsMeasure volume V] ℝ),
      (classicalEigenRepresentative_spec V ρ u).2.2,
      (compactGibbsRepresentative_spec V v).2.2] with x hs hu hv
    rw [hs, Pi.smul_apply, smul_eq_mul, ← hu, ← hv, Real.inner_apply]
    ring
  have hright : inner ℝ (u : E →₂[gibbsMeasure volume V] ℝ) (compactGibbsGenerator hV hprob v) =
      ∫ x, classicalEigenRepresentative V ρ u x *
        langevinDifferentialOperator V (compactGibbsRepresentative V v) x ∂gibbsMeasure volume V
          := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(classicalEigenRepresentative_spec V ρ u).2.2,
      compactGibbsGenerator_coeFn hV hprob v] with x hu hv
    rw [← hu, hv, Real.inner_apply]
  rw [hright, gibbs_generator_green_one_compact hV (classicalEigenRepresentative_spec V ρ u).1
    (compactGibbsRepresentative_spec V v).1 (compactGibbsRepresentative_spec V v).2.1]
  simpa only [(classicalEigenRepresentative_spec V ρ u).2.1] using hleft

/-- Every actual classical eigenclass lies in the genuine adjoint operator domain. -/
theorem classicalEigen_mem_compactGenerator_adjoint_domain {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ)
    (u : classicalL2Eigenspace V ρ) :
    (u : E →₂[gibbsMeasure volume V] ℝ) ∈ (compactGibbsGenerator hV hprob)†.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists
  exact ⟨(-ρ) • (u : E →₂[gibbsMeasure volume V] ℝ),
    classicalEigen_compactGenerator_adjoint_pairing hV hprob ρ u⟩

/-- The actual adjoint operator acts on each classical eigenclass by its
stated eigenvalue. This is a proved inclusion, not an asserted domain equality. -/
theorem compactGibbsGenerator_adjoint_classicalEigen {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (ρ : ℝ)
    (u : classicalL2Eigenspace V ρ) :
    (compactGibbsGenerator hV hprob)†
      ⟨(u : E →₂[gibbsMeasure volume V] ℝ),
        classicalEigen_mem_compactGenerator_adjoint_domain hV hprob ρ u⟩ =
      (-ρ) • (u : E →₂[gibbsMeasure volume V] ℝ) := by
  exact LinearPMap.adjoint_apply_eq (T := compactGibbsGenerator hV hprob)
    (compactGibbsGeneratorDomain_dense V hprob) _
    (classicalEigen_compactGenerator_adjoint_pairing hV hprob ρ u)

end CutoffRigidity
