/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalDuality
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.EuclideanWspLpMembership
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.LocalCoarseGrainingDefinitions

/-!
# HomCGFinalDatum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The printed data hypothesis `𝐠 ∈ W^{s₂,p}(□_m)`, from the root's own binder

## What this file supplies

The measurement named ONE printed hypothesis the spine's bundle does not carry:
the coarse-graining display's data membership `𝐠 ∈ W^{s₂,p}(□_m)`. It is not an
extra assumption — it follows from the root's OWN `C^{0,1/2}` binder on `𝐠`,
which the spine already quantifies, by the same embedding `HomCGFinalGagliardo`
supplies, read at `(α, s′) = (1/2, s₂)`.

* `memCubeEuclideanFullWsp_of_holder` — the general statement;
* `memCubeEuclideanFullWsp_of_holderHalf` — the pinned instance at `α = 1/2`;
* `holderHalf_window` — the admissible `s₂` band: `1/2 - d/p < s₂ < 1/2`.

At the pin `p = 4d` the band is `1/4 < s₂ < 1/2`, which is compatible with the
bundle's own `s < s₂ < 1` whenever `s < 1/4` — and the bundle's guard
`s + d/p ≤ 1/2` gives exactly `s ≤ 1/4` at that pin.  The band is nonempty and
`s₂` is existentially quantified by the bundle, so nothing is over-determined.

## The two subtype bridges

`mkFractionalOrder` and `mkFiniteLpExponent` build `CoarseGraining`'s carriers
from raw reals; both come with the `toReal` computation, so a consumer working
with the manuscript's numerals never has to unfold a subtype.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 2. The `L^p` half from the Hölder binder -/

/-- **A `C^{0,α}` field on `□_m` is in `L^p` of the normalized cube measure.** -/
theorem memLp_ofVec_of_holderSeminormBoundOn_originCube {m : ℤ} {alpha K : ℝ}
    {p : FiniteLpExponent} {g : Vec d → Vec d} (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hg : HolderSeminormBoundOn (openCubeSet (originCube d m)) alpha K g) :
    MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure (originCube d m)) := by
  have : IsFiniteMeasure (normalizedCubeMeasure (originCube d m)) :=
    normalizedCubeMeasure.instIsFiniteMeasure _
  have hcont : ContinuousOn g (openCubeSet (originCube d m)) :=
    Schauder.continuousOn_of_holderSeminormBoundOn hK halpha hg
  have hmeasRestrict : AEStronglyMeasurable g
      (volume.restrict (openCubeSet (originCube d m))) :=
    hcont.aestronglyMeasurable (measurableSet_openCubeSet (originCube d m))
  have hmeas : AEStronglyMeasurable g (normalizedCubeMeasure (originCube d m)) := by
    rw [normalizedCubeMeasure_eq_smul_restrict_openCubeSet]
    exact hmeasRestrict.smul_measure _
  have hofVec : AEStronglyMeasurable (fun x => HilbertVec.ofVec (g x))
      (normalizedCubeMeasure (originCube d m)) :=
    (HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable hmeas
  refine MemLp.of_bound hofVec ((d : ℝ) * (‖g 0‖ + K * ((3 : ℝ) ^ m) ^ alpha)) ?_
  filter_upwards [ae_mem_openCubeSet (originCube d m)] with x hx
  have hb := Schauder.norm_le_of_holderSeminormBoundOn_originCube hK halpha.le hg hx
  have hnorm : ‖HilbertVec.ofVec (g x)‖ = euclideanNorm (g x) :=
    (euclideanNorm_eq_norm_ofVec (g x)).symm
  rw [hnorm]
  exact (euclideanNorm_le_dimension_mul_norm (g x)).trans
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg d))

/-! ## 3. The full fractional membership -/

/-- **`C^{0,α}(□_m) ⊂ W^{s₂,p}(□_m)`, at `CoarseGraining`'s membership predicate.** -/
theorem memCubeEuclideanFullWsp_of_holder {m : ℤ} {s2 : FractionalOrder}
    {p : FiniteLpExponent} {alpha K : ℝ} {g : Vec d → Vec d}
    (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hlo : 0 < (alpha - s2.1) * p.exponent.toReal)
    (hhi : (alpha - s2.1) * p.exponent.toReal < (d : ℝ))
    (hg : HolderSeminormBoundOn (openCubeSet (originCube d m)) alpha K g) :
    MemCubeEuclideanFullWsp (originCube d m) s2 p g := by
  have hLp := memLp_ofVec_of_holderSeminormBoundOn_originCube (p := p) hK halpha hg
  have hsemi : cubeEuclideanWspESeminorm (originCube d m) s2 p g < ⊤ :=
    lt_of_le_of_lt (cubeEuclideanWspESeminorm_le_of_holder hK hlo hhi hg)
      ENNReal.ofReal_lt_top
  exact ⟨hLp, memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top hLp hsemi⟩

/-- **The admissible `s₂` band at the Hölder exponent `1/2`.** -/
theorem holderHalf_window {p : FiniteLpExponent} {s2 : ℝ}
    (hlt : s2 < 1 / 2) (hgt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2) :
    0 < (1 / 2 - s2) * p.exponent.toReal ∧
      (1 / 2 - s2) * p.exponent.toReal < (d : ℝ) := by
  have htpos : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  have hdiff : 0 < 1 / 2 - s2 := by linarith only [hlt]
  refine ⟨mul_pos hdiff htpos, ?_⟩
  have hstep : 1 / 2 - s2 < (d : ℝ) / p.exponent.toReal := by linarith only [hgt]
  have hmul := mul_lt_mul_of_pos_right hstep htpos
  rwa [div_mul_cancel₀ _ (ne_of_gt htpos)] at hmul

/-- **The pinned instance: the root's own `C^{0,1/2}` binder on `𝐠` supplies the
printed data hypothesis `𝐠 ∈ W^{s₂,p}(□_m)`.** -/
theorem memCubeEuclideanFullWsp_of_holderHalf {m : ℤ} {s2 : FractionalOrder}
    {p : FiniteLpExponent} {K : ℝ} {g : Vec d → Vec d} (hK : 0 ≤ K)
    (hlt : s2.1 < 1 / 2) (hgt : 1 / 2 - (d : ℝ) / p.exponent.toReal < s2.1)
    (hg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    MemCubeEuclideanFullWsp (originCube d m) s2 p g := by
  obtain ⟨hlo, hhi⟩ := holderHalf_window (p := p) hlt hgt
  exact memCubeEuclideanFullWsp_of_holder hK (by norm_num) hlo hhi hg

end

end Algsuperdiff.Section4.Provider.Homogenization
