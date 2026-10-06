/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicCube
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CoerciveH1
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# High-contrast homogenization: Provider.Regularity.LocalGradientTopology

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A countable local-gradient topology

Local weak gradients are represented by compatible `L²` classes on the
centered open triadic cubes.  The resulting countable projective carrier has
the product topology and measurable structure, so measurable finite-volume
gradients can be passed to coordinatewise limits without choosing pointwise
representatives.
-/

open scoped ENNReal

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

/-- The `n`th member of the centered open-cube exhaustion of `Vec d`. -/
@[expose]
def localGradientCube (d n : ℕ) : Set (Vec d) :=
  openCubeSet (originCube d (n : ℤ))

/-- Centered cubes in the local-gradient exhaustion are nested. -/
theorem localGradientCube_mono {d m n : ℕ} (hmn : m ≤ n) :
    localGradientCube d m ⊆ localGradientCube d n := by
  intro x hx
  rw [localGradientCube, mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  have hpow : (3 : ℝ) ^ (m : ℤ) ≤ (3 : ℝ) ^ (n : ℤ) := by
    exact zpow_le_zpow_right₀ (by norm_num) (Int.ofNat_le.mpr hmn)
  constructor <;> linarith only [hlo, hhi, hpow]

/-- The centered cubes exhaust the whole Euclidean space. -/
theorem iUnion_localGradientCube (d : ℕ) :
    ⋃ n, localGradientCube d n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rw [Set.mem_iUnion]
  obtain ⟨n, hn⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).eventually_gt_atTop
      (2 * ‖x‖)).exists
  refine ⟨n, ?_⟩
  rw [localGradientCube, mem_openCubeSet_originCube_iff]
  intro i
  have hcoord : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hn' : 2 * ‖x‖ < (3 : ℝ) ^ (n : ℤ) := by
    simpa only [zpow_natCast] using hn
  constructor <;>
    linarith only [neg_abs_le (x i), le_abs_self (x i), hcoord, hn']

/-- Hilbert-valued `L²` gradients on one member of the exhaustion. -/
abbrev LocalGradientL2 (d n : ℕ) :=
  HilbertVectorL2 (localGradientCube d n)

private instance (d n : ℕ) : Module ℝ (LocalGradientL2 d n) := inferInstance

@[expose]
public noncomputable def localGradientRestrictLinear {d m n : ℕ} (hmn : m ≤ n) :
    LocalGradientL2 d n →ₗ[ℝ] LocalGradientL2 d m where
  toFun g :=
    ((Lp.memLp g).mono_measure
      (Measure.restrict_mono_set volume (localGradientCube_mono hmn))).toLp g
  map_add' f g := by
    let hmu : volumeMeasureOn (localGradientCube d m) ≤
        volumeMeasureOn (localGradientCube d n) :=
      Measure.restrict_mono_set volume (localGradientCube_mono hmn)
    change
      ((Lp.memLp (f + g)).mono_measure hmu).toLp (f + g) =
        ((Lp.memLp f).mono_measure hmu).toLp f +
          ((Lp.memLp g).mono_measure hmu).toLp g
    exact
      (MemLp.toLp_congr
        ((Lp.memLp (f + g)).mono_measure hmu)
        (((Lp.memLp f).mono_measure hmu).add ((Lp.memLp g).mono_measure hmu))
        ((Lp.coeFn_add f g).filter_mono (ae_mono hmu))).trans
      (MemLp.toLp_add
        ((Lp.memLp f).mono_measure hmu) ((Lp.memLp g).mono_measure hmu))
  map_smul' c f := by
    let hmu : volumeMeasureOn (localGradientCube d m) ≤
        volumeMeasureOn (localGradientCube d n) :=
      Measure.restrict_mono_set volume (localGradientCube_mono hmn)
    change
      ((Lp.memLp (c • f : LocalGradientL2 d n)).mono_measure hmu).toLp
          (c • f : LocalGradientL2 d n) =
        (c • ((Lp.memLp f).mono_measure hmu).toLp f : LocalGradientL2 d m)
    exact
      (MemLp.toLp_congr
        ((Lp.memLp (c • f : LocalGradientL2 d n)).mono_measure hmu)
        (((Lp.memLp f).mono_measure hmu).const_smul c)
        ((Lp.coeFn_smul c f).filter_mono (ae_mono hmu))).trans
      (MemLp.toLp_const_smul c ((Lp.memLp f).mono_measure hmu))

private theorem localGradientRestrictLinear_norm_le {d m n : ℕ} (hmn : m ≤ n)
    (g : LocalGradientL2 d n) :
    ‖localGradientRestrictLinear hmn g‖ ≤ ‖g‖ := by
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  change ‖((Lp.memLp g).mono_measure hmu).toLp g‖ ≤ ‖g‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (eLpNorm_mono_measure g hmu)

/-- Restriction of an `L²` a.e. class from a larger exhaustion cube to a
smaller one. -/
@[expose]
noncomputable def localGradientRestrict {d m n : ℕ} (hmn : m ≤ n) :
    LocalGradientL2 d n →L[ℝ] LocalGradientL2 d m :=
  LinearMap.mkContinuous (localGradientRestrictLinear hmn) 1 fun g => by
    simpa only [one_mul] using localGradientRestrictLinear_norm_le hmn g

/-- Restriction agrees almost everywhere with the same local representative. -/
theorem localGradientRestrict_coeFn_ae {d m n : ℕ} (hmn : m ≤ n)
    (g : LocalGradientL2 d n) :
    localGradientRestrict hmn g =ᵐ[volumeMeasureOn (localGradientCube d m)] g := by
  exact MemLp.coeFn_toLp
    ((Lp.memLp g).mono_measure
      (Measure.restrict_mono_set volume (localGradientCube_mono hmn)))

/-- The restricted class is characterized by any representative which agrees
with the original class almost everywhere on the smaller cube. -/
theorem localGradientRestrict_eq_iff_ae {d m n : ℕ} (hmn : m ≤ n)
    (g : LocalGradientL2 d n) (h : LocalGradientL2 d m) :
    localGradientRestrict hmn g = h ↔
      g =ᵐ[volumeMeasureOn (localGradientCube d m)] h := by
  constructor
  · intro heq
    have hrep := localGradientRestrict_coeFn_ae hmn g
    rw [heq] at hrep
    exact hrep.symm
  · intro hrep
    apply Lp.ext
    exact (localGradientRestrict_coeFn_ae hmn g).trans hrep

/-- Restricting to the same cube is the identity. -/
@[simp] theorem localGradientRestrict_refl {d n : ℕ} :
    localGradientRestrict (d := d) (le_refl n) =
      ContinuousLinearMap.id ℝ (LocalGradientL2 d n) := by
  apply ContinuousLinearMap.ext
  intro g
  apply Lp.ext
  exact localGradientRestrict_coeFn_ae (le_refl n) g

/-- Compatible local `L²` classes form the projective local-gradient
submodule. -/
@[expose]
noncomputable def localGradientProjectiveSubmodule (d : ℕ) :
    Submodule ℝ ((n : ℕ) → LocalGradientL2 d n) where
  carrier := {g | ∀ m n (hmn : m ≤ n), localGradientRestrict hmn (g n) = g m}
  zero_mem' := by
    intro m n hmn
    exact (localGradientRestrict hmn).map_zero
  add_mem' := by
    intro f g hf hg m n hmn
    change localGradientRestrict hmn (f n + g n) = f m + g m
    rw [(localGradientRestrict hmn).map_add, hf m n hmn, hg m n hmn]
  smul_mem' := by
    intro c f hf m n hmn
    change localGradientRestrict hmn (c • f n : LocalGradientL2 d n) =
      (c • f m : LocalGradientL2 d m)
    rw [(localGradientRestrict hmn).map_smul, hf m n hmn]

/-- The countable projective carrier for local weak-gradient classes. -/
noncomputable abbrev LocalGradientCarrier (d : ℕ) :=
  localGradientProjectiveSubmodule d

namespace LocalGradientCarrier

/-- The local `L²` class on the `n`th exhaustion cube. -/
@[expose]
def component {d : ℕ} (g : LocalGradientCarrier d) (n : ℕ) :
    LocalGradientL2 d n :=
  g.1 n

/-- Components agree under restriction to every smaller exhaustion cube. -/
theorem restrict_component {d : ℕ} (g : LocalGradientCarrier d)
    {m n : ℕ} (hmn : m ≤ n) :
    localGradientRestrict hmn (component g n) = component g m :=
  g.2 m n hmn

/-- A projective local gradient is determined by its local components. -/
@[ext] theorem ext {d : ℕ} {f g : LocalGradientCarrier d}
    (h : ∀ n, component f n = component g n) : f = g := by
  apply Subtype.ext
  funext n
  exact h n

end LocalGradientCarrier

end

end HighContrast
end HCPolySupport
