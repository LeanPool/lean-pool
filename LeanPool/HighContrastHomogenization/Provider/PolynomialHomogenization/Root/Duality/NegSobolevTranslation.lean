/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers
public import LeanPool.HighContrastHomogenization.Support.Geometry.Translation

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Duality.NegSobolevTranslation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Translation invariance of the normalized fractional norms

The gauge image of an adapted-cell witness is a triadic cube translated by an
arbitrary real vector, so the cube-side estimate has to be moved by a
translation that is not a lattice translation.  Every norm entering the
negative fractional dual is translation invariant; this file records that, for
`hsNormSq`, `fracSeminormSq`, the dual pairing, and `negSobolevNorm`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Lower integrals over a translate. -/
private theorem lintegral_translateSet (z : Vec d) (V : Set (Vec d))
    (g : Vec d → ℝ≥0∞) :
    ∫⁻ x in translateSet z V, g x ∂volume =
      ∫⁻ x in V, g (x + z) ∂volume :=
  ((measurePreserving_addRight_restrict_translateSet z V).lintegral_comp_emb
    (Homeomorph.addRight z).measurableEmbedding g).symm

/-- Normalized lower averages over a translate. -/
private theorem eVolumeAverage_translateSet (z : Vec d) (V : Set (Vec d))
    (g : Vec d → ℝ≥0∞) :
    eVolumeAverage (translateSet z V) g =
      eVolumeAverage V (fun x => g (x + z)) := by
  unfold eVolumeAverage
  rw [lintegral_translateSet, volume_translateSet_eq]

/-- The fractional seminorm square is translation invariant. -/
theorem fracSeminormSq_translateSet (z : Vec d) (V : Set (Vec d)) (s : ℝ)
    (F : Vec d → Vec d) :
    fracSeminormSq (translateSet z V) s (fun x => F (x - z)) =
      fracSeminormSq V s F := by
  unfold fracSeminormSq
  rw [eVolumeAverage_translateSet]
  refine congrArg (eVolumeAverage V) ?_
  funext x
  rw [lintegral_translateSet]
  refine lintegral_congr fun y => ?_
  have hx : x + z - z = x := by abel
  have hy : y + z - z = y := by abel
  have hxy : x + z - (y + z) = x - y := by abel
  simp only [hx, hy, hxy]

/-- The normalized `H^s` norm square is translation invariant. -/
theorem hsNormSq_translateSet (z : Vec d) (V : Set (Vec d)) (s : ℝ)
    (F : Vec d → Vec d) :
    hsNormSq (translateSet z V) s (fun x => F (x - z)) = hsNormSq V s F := by
  unfold hsNormSq
  rw [volume_translateSet_eq, eVolumeAverage_translateSet,
    fracSeminormSq_translateSet]
  refine congrArg (fun t => volume V ^ (-(2 * s) / (d : ℝ)) * t +
    fracSeminormSq V s F) ?_
  refine congrArg (eVolumeAverage V) ?_
  funext x
  have hx : x + z - z = x := by abel
  simp only [hx]

/-- A local vector test translates. -/
theorem IsLocalVecTest.translate {V : Set (Vec d)} {psi : Vec d → Vec d}
    (h : IsLocalVecTest V psi) (z : Vec d) :
    IsLocalVecTest (translateSet z V) (fun x => psi (x - z)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg, Function.comp_def] using
      h.contDiff.comp (contDiff_id.sub contDiff_const)
  · show HasCompactSupport (psi ∘ Homeomorph.subRight z)
    simpa [Function.comp_def] using
      h.hasCompactSupport.comp_homeomorph (Homeomorph.subRight z)
  · intro x hx
    have hx' : x - z ∈ tsupport psi := by
      rw [show (fun y => psi (y - z)) = psi ∘ Homeomorph.subRight z from rfl,
        tsupport_comp_eq_preimage psi (Homeomorph.subRight z)] at hx
      exact hx
    exact (mem_translateSet_iff_sub_mem).2 (h.tsupport_subset hx')

/-- The dual pairing is translation invariant. -/
theorem dualPairing_translateSet (z : Vec d) (V : Set (Vec d))
    (F psi : Vec d → Vec d) :
    dualPairing (translateSet z V) (fun x => F (x - z))
        (fun x => psi (x - z)) =
      dualPairing V F psi := by
  have hiff : IntegrableOn (fun x => vecDot (F (x - z)) (psi (x - z)))
      (translateSet z V) volume ↔
      IntegrableOn (fun x => vecDot (F x) (psi x)) V volume :=
    (measurePreserving_subRight_restrict_translateSet z V).integrable_comp_emb
      (Homeomorph.subRight z).measurableEmbedding
      (g := fun y : Vec d => vecDot (F y) (psi y))
  simp only [dualPairing]
  by_cases h : IntegrableOn (fun x => vecDot (F x) (psi x)) V volume
  · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
    refine congrArg ENNReal.ofReal ?_
    unfold volumeAverage
    rw [volume_translateSet_eq,
      setIntegral_comp_subRight_translateSet z V
        (fun y : Vec d => vecDot (F y) (psi y))]
  · rw [ite_eq_right (fun hcon => h (hiff.1 hcon)), ite_eq_right h]

/-- One direction of the translation invariance of the dual fractional norm. -/
theorem negSobolevNorm_translateSet_le (z : Vec d) (V : Set (Vec d)) (s : ℝ)
    (F : Vec d → Vec d) :
    negSobolevNorm (translateSet z V) s (fun x => F (x - z)) ≤
      negSobolevNorm V s F := by
  unfold negSobolevNorm
  refine iSup_le ?_
  rintro ⟨psi, htest, hnorm⟩
  have hset : translateSet (-z) (translateSet z V) = V := by
    rw [translateSet_translateSet]
    simp
  have htest' : IsLocalVecTest V (fun x => psi (x + z)) := by
    have h := IsLocalVecTest.translate htest (-z)
    rw [hset] at h
    simpa [sub_neg_eq_add] using h
  have hnormEq : hsNormSq V s (fun x => psi (x + z)) =
      hsNormSq (translateSet z V) s psi := by
    have h := hsNormSq_translateSet (-z) (translateSet z V) s psi
    rw [hset] at h
    simpa [sub_neg_eq_add] using h
  have hnorm' : hsNormSq V s (fun x => psi (x + z)) ≤ 1 := by
    rw [hnormEq]
    exact hnorm
  have hpsi : (fun x : Vec d => (fun y => psi (y + z)) (x - z)) = psi := by
    funext x
    have hx : x - z + z = x := by abel
    simp only [hx]
  have hpair : dualPairing (translateSet z V) (fun x => F (x - z)) psi =
      dualPairing V F (fun x => psi (x + z)) := by
    have h := dualPairing_translateSet z V F (fun y => psi (y + z))
    rwa [hpsi] at h
  rw [hpair]
  exact le_iSup (fun t : {psi' : Vec d → Vec d //
      IsLocalVecTest V psi' ∧ hsNormSq V s psi' ≤ 1} => dualPairing V F t.1)
    ⟨_, htest', hnorm'⟩

/-- **The dual fractional norm is translation invariant.** -/
theorem negSobolevNorm_translateSet (z : Vec d) (V : Set (Vec d)) (s : ℝ)
    (F : Vec d → Vec d) :
    negSobolevNorm (translateSet z V) s (fun x => F (x - z)) =
      negSobolevNorm V s F := by
  refine le_antisymm (negSobolevNorm_translateSet_le z V s F) ?_
  have hset : translateSet (-z) (translateSet z V) = V := by
    rw [translateSet_translateSet]
    simp
  have h := negSobolevNorm_translateSet_le (-z) (translateSet z V) s
    (fun x => F (x - z))
  rw [hset] at h
  have hfield : (fun x : Vec d => (fun y => F (y - z)) (x - -z)) = F := by
    funext x
    have hx : x - -z - z = x := by abel
    simp only [hx]
  rwa [hfield] at h

end

end RowSupply
end HighContrast
end HCPolySupport
