/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.AssocPressureProviderBounds

/-!
# Eventual equality for Helmholtz cutoffs

Cutoff derivatives agree pointwise with the uncut Helmholtz decomposition.
-/

public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal
open scoped Convolution
open scoped Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

/-- Spatial derivatives of the Helmholtz cutoffs eventually equal those of
the original test, as used in `thm:assoc-pressure`. -/
theorem associatedPressureHelmholtzTestCutoff_spatial_eventually_eq
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i j : Fin 3) (z : Vec3 × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      CKN.spatialPartialProd
        (fun q => associatedPressureHelmholtzTestCutoff φ n q i) j z =
      CKN.spatialPartialProd (fun q => φ q i) j z := by
  let A := associatedPressureHelmholtzCutoffVectorPotential φ
  let v n : Vec3 × ℝ → Vec3 := associatedPressureTestCurl (A n)
  let g n : Vec3 × ℝ → Vec3 := associatedPressureTestGradient
    (associatedPressureHelmholtzScalarPotentialCutoff φ n)
  let v₀ : Vec3 × ℝ → Vec3 :=
    associatedPressureTestCurl (associatedPressureHelmholtzVectorPotential φ)
  let g₀ : Vec3 × ℝ → Vec3 := associatedPressureTestGradient
    (associatedPressureHelmholtzScalarPotential φ)
  have hVn (n : ℕ) := associatedPressureTestCurl_mem_spaceTimeTestFunction
    (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n)
  have hGn (n : ℕ) :=
    associatedPressureHelmholtzScalarPotentialCutoffGradient_mem_spaceTimeTestFunction hφ n
  have hV₀ : ContDiff ℝ (⊤ : ℕ∞) v₀ := by
    have hA := associatedPressureHelmholtzVectorPotential_contDiff hφ
    exact associatedPressureTestCurl_contDiff hA
  have hG₀ : ContDiff ℝ (⊤ : ℕ∞) g₀ := by
    have hψ : ContDiff ℝ (⊤ : ℕ∞)
        (associatedPressureHelmholtzScalarPotential φ) :=
      associatedPressureHelmholtzScalarPotential_contDiff hφ
    apply contDiff_pi.2
    intro k
    exact CKN.spatialPartial_contDiff hψ k
  have hsplit (q : Vec3 × ℝ) : φ q = v₀ q + g₀ q := by
    have hcurl : associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) =
          associatedPressureTestCurl (associatedPressureHelmholtzVectorPotential φ) := by
      funext z k
      fin_cases k <;> rfl
    change φ q = associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) q +
      associatedPressureTestGradient
        (associatedPressureHelmholtzScalarPotential φ) q
    calc
      φ q = associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) q +
          associatedPressureTestGradient
            (associatedPressureHelmholtzScalarPotential φ) q :=
        associatedPressureHelmholtz_identity hφ q
      _ = _ := by rw [hcurl]
  have hsplit_i : (fun q => φ q i) = (fun q => v₀ q i + g₀ q i) := by
    funext q
    exact congrArg (fun w : Vec3 => w i) (hsplit q)
  have hbase := associatedPressureSpatialPartialProd_add
    ((contDiff_apply ℝ ℝ i).comp hV₀) ((contDiff_apply ℝ ℝ i).comp hG₀) j z
  have huncut : CKN.spatialPartialProd (fun q => φ q i) j z =
      CKN.spatialPartialProd (fun q => v₀ q i) j z +
        CKN.spatialPartialProd (fun q => g₀ q i) j z := by
    calc
      _ = CKN.spatialPartialProd (fun q => v₀ q i + g₀ q i) j z := by
        exact congrArg (fun f : Vec3 × ℝ → ℝ => CKN.spatialPartialProd f j z)
          hsplit_i
      _ = _ := hbase
  have hv := associatedPressureHelmholtzCutoffCurl_spatial_eventually_eq
    hφ i j z
  have hg := associatedPressureHelmholtzScalarPotentialCutoff_spatial_eventually_eq
    hφ i j z
  filter_upwards [hv, hg] with n hve hge
  have hge' : CKN.spatialPartialProd (fun q => g n q i) j z =
      CKN.spatialPartialProd (fun q => g₀ q i) j z := by
    change CKN.spatialSecondPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) i j z =
      CKN.spatialSecondPartialProd
        (associatedPressureHelmholtzScalarPotential φ) i j z
    exact hge
  have hsum : CKN.spatialPartialProd (fun q => v n q i + g n q i) j z =
      CKN.spatialPartialProd (fun q => v n q i) j z +
        CKN.spatialPartialProd (fun q => g n q i) j z :=
    associatedPressureSpatialPartialProd_add
      ((contDiff_apply ℝ ℝ i).comp (hVn n).1)
      ((contDiff_apply ℝ ℝ i).comp (hGn n).1) j z
  change CKN.spatialPartialProd (fun q => v n q i + g n q i) j z = _
  rw [hsum, hve, hge', huncut]

/-- Time derivatives of the Helmholtz cutoffs eventually equal those of the
original test, as used in `thm:assoc-pressure`. -/
theorem associatedPressureHelmholtzTestCutoff_time_eventually_eq
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i : Fin 3) (z : Vec3 × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      CKN.timePartialProd
        (fun q => associatedPressureHelmholtzTestCutoff φ n q i) z =
      CKN.timePartialProd (fun q => φ q i) z := by
  let A := associatedPressureHelmholtzCutoffVectorPotential φ
  let v n : Vec3 × ℝ → Vec3 := associatedPressureTestCurl (A n)
  let g n : Vec3 × ℝ → Vec3 := associatedPressureTestGradient
    (associatedPressureHelmholtzScalarPotentialCutoff φ n)
  let v₀ : Vec3 × ℝ → Vec3 :=
    associatedPressureTestCurl (associatedPressureHelmholtzVectorPotential φ)
  let g₀ : Vec3 × ℝ → Vec3 := associatedPressureTestGradient
    (associatedPressureHelmholtzScalarPotential φ)
  have hVn (n : ℕ) := associatedPressureTestCurl_mem_spaceTimeTestFunction
    (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n)
  have hGn (n : ℕ) :=
    associatedPressureHelmholtzScalarPotentialCutoffGradient_mem_spaceTimeTestFunction hφ n
  have hV₀ : ContDiff ℝ (⊤ : ℕ∞) v₀ := by
    have hA := associatedPressureHelmholtzVectorPotential_contDiff hφ
    exact associatedPressureTestCurl_contDiff hA
  have hG₀ : ContDiff ℝ (⊤ : ℕ∞) g₀ := by
    have hψ : ContDiff ℝ (⊤ : ℕ∞)
        (associatedPressureHelmholtzScalarPotential φ) :=
      associatedPressureHelmholtzScalarPotential_contDiff hφ
    apply contDiff_pi.2
    intro k
    exact CKN.spatialPartial_contDiff hψ k
  have hsplit (q : Vec3 × ℝ) : φ q = v₀ q + g₀ q := by
    have hcurl : associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) =
          associatedPressureTestCurl (associatedPressureHelmholtzVectorPotential φ) := by
      funext w k
      fin_cases k <;> rfl
    change φ q = associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) q +
      associatedPressureTestGradient
        (associatedPressureHelmholtzScalarPotential φ) q
    calc
      φ q = associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) q +
          associatedPressureTestGradient
            (associatedPressureHelmholtzScalarPotential φ) q :=
        associatedPressureHelmholtz_identity hφ q
      _ = _ := by rw [hcurl]
  have hsplit_i : (fun q => φ q i) = (fun q => v₀ q i + g₀ q i) := by
    funext q
    exact congrArg (fun w : Vec3 => w i) (hsplit q)
  have hbase := associatedPressureTimePartialProd_add
    ((contDiff_apply ℝ ℝ i).comp hV₀) ((contDiff_apply ℝ ℝ i).comp hG₀) z
  have huncut : CKN.timePartialProd (fun q => φ q i) z =
      CKN.timePartialProd (fun q => v₀ q i) z +
        CKN.timePartialProd (fun q => g₀ q i) z := by
    calc
      _ = CKN.timePartialProd (fun q => v₀ q i + g₀ q i) z := by
        exact congrArg (fun f : Vec3 × ℝ → ℝ => CKN.timePartialProd f z) hsplit_i
      _ = _ := hbase
  have hv := associatedPressureHelmholtzCutoffCurl_timePartial_eventually_eq
    hφ i z
  have hg := associatedPressureHelmholtzScalarPotentialCutoff_timeSpatial_eventually_eq
    hφ i z
  filter_upwards [hv, hg] with n hve hge
  have hve' : CKN.timePartialProd (fun q => v n q i) z =
      CKN.timePartialProd (fun q => v₀ q i) z := by
    convert hve using 1 <;> rfl
  have hge' : CKN.timePartialProd (fun q => g n q i) z =
      CKN.timePartialProd (fun q => g₀ q i) z := by
    change CKN.timePartialProd
        (CKN.spatialPartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φ n) i) z =
      CKN.timePartialProd
        (CKN.spatialPartialProd
          (associatedPressureHelmholtzScalarPotential φ) i) z
    exact hge
  have hsum : CKN.timePartialProd (fun q => v n q i + g n q i) z =
      CKN.timePartialProd (fun q => v n q i) z +
        CKN.timePartialProd (fun q => g n q i) z :=
    associatedPressureTimePartialProd_add
      ((contDiff_apply ℝ ℝ i).comp (hVn n).1)
      ((contDiff_apply ℝ ℝ i).comp (hGn n).1) z
  change CKN.timePartialProd (fun q => v n q i + g n q i) z = _
  rw [hsum, hve', hge', huncut]

end CKN.Leray

end
