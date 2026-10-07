/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUZeroExtendScalarWeak

/-!
# Weak derivatives after compact zero extension

A compactly supported field with globally square-integrable derivative data
inherits its weak identities on every larger cylinder containing that data.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Compactly supported weak derivative data extend from a source cylinder
to a target cylinder containing their support. -/
theorem bu_weak_extend_compact
    {Ω Ω' : Set Vec3} {I I' : Set ℝ} {K : Set ParabolicPoint}
    (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hKcompact : IsCompact K)
    (hKsource : K ⊆ spaceTimeSet Ω I)
    (hKtarget : K ⊆ spaceTimeSet Ω' I')
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hzero : ∀ z ∉ K, w z = 0 ∧ Dw z = 0 ∧ D2w z = 0 ∧ Dtw z = 0)
    (hweak : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hmem : MemLp w 2 volume ∧ MemLp Dw 2 volume ∧
      MemLp D2w 2 volume ∧ MemLp Dtw 2 volume) :
    HasSpaceTimeWeakDerivs Ω' I' w Dw D2w Dtw := by
  have hsupport : Function.support w ⊆ K := by
    intro z hz
    by_contra hnot
    exact hz (hzero z hnot).1
  have hcompact : HasCompactSupport w :=
    HasCompactSupport.of_support_subset_isCompact hKcompact hsupport
  have htsupport : tsupport w ⊆ spaceTimeSet Ω I :=
    (closure_minimal hsupport hKcompact.isClosed).trans hKsource
  have hglobal := spaceTimeZeroExtensions_weak_derivatives
    hΩ hI hweak hcompact htsupport
  have hWloc : LocallyIntegrableOn w (spaceTimeSet Ω' I') volume :=
    (hmem.1.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hDwloc : LocallyIntegrableOn Dw (spaceTimeSet Ω' I') volume :=
    (hmem.2.1.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hD2loc : LocallyIntegrableOn D2w (spaceTimeSet Ω' I') volume :=
    (hmem.2.2.1.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hDtloc : LocallyIntegrableOn Dtw (spaceTimeSet Ω' I') volume :=
    (hmem.2.2.2.locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hWzero (i : Fin 3) (z : ParabolicPoint) (hz : z ∉ K) :
      w z i = 0 := congrArg (· i) (hzero z hz).1
  have hDwzero (i j : Fin 3) (z : ParabolicPoint) (hz : z ∉ K) :
      Dw z i j = 0 := congrArg (fun F => F i j) (hzero z hz).2.1
  have hD2zero (i j k : Fin 3) (z : ParabolicPoint) (hz : z ∉ K) :
      D2w z i j k = 0 :=
    congrArg (fun F => F i j k) (hzero z hz).2.2.1
  have hDtzero (i : Fin 3) (z : ParabolicPoint) (hz : z ∉ K) :
      Dtw z i = 0 := congrArg (· i) (hzero z hz).2.2.2
  have hEqW (i : Fin 3) (q : Vec3 × ℝ) :
      zeroExtendField (Ω ×ˢ I)
        (fun r : Vec3 × ℝ => w (parabolicHomeomorph.symm r) i) q =
          w (parabolicHomeomorph.symm q) i :=
    bu_zeroExtend_eq_of_support_subset hKsource (hWzero i) q
  have hEqDw (i j : Fin 3) (q : Vec3 × ℝ) :
      zeroExtendField (Ω ×ˢ I)
        (fun r : Vec3 × ℝ => Dw (parabolicHomeomorph.symm r) i j) q =
          Dw (parabolicHomeomorph.symm q) i j :=
    bu_zeroExtend_eq_of_support_subset hKsource (hDwzero i j) q
  have hEqD2 (i j k : Fin 3) (q : Vec3 × ℝ) :
      zeroExtendField (Ω ×ˢ I)
        (fun r : Vec3 × ℝ => D2w (parabolicHomeomorph.symm r) i j k) q =
          D2w (parabolicHomeomorph.symm q) i j k :=
    bu_zeroExtend_eq_of_support_subset hKsource (hD2zero i j k) q
  have hEqDt (i : Fin 3) (q : Vec3 × ℝ) :
      zeroExtendField (Ω ×ˢ I)
        (fun r : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm r) i) q =
          Dtw (parabolicHomeomorph.symm q) i :=
    bu_zeroExtend_eq_of_support_subset hKsource (hDtzero i) q
  refine ⟨hWloc, hDwloc, hD2loc, hDtloc, ?_⟩
  intro φ hφ
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    apply bu_spatial_weak_identity_of_global hKtarget
      (fun z => w z i) (fun z => Dw z i j)
      (hWzero i) (hDwzero i j) j _ φ hφ
    intro ψ hψ hψc
    have h := hglobal.1 i j ψ hψ hψc
    simp_rw [hEqW i, hEqDw i j] at h
    exact h
  · intro i j k
    apply bu_spatial_weak_identity_of_global hKtarget
      (fun z => Dw z i j) (fun z => D2w z i j k)
      (hDwzero i j) (hD2zero i j k) k _ φ hφ
    intro ψ hψ hψc
    have h := hglobal.2.1 i j k ψ hψ hψc
    simp_rw [hEqDw i j, hEqD2 i j k] at h
    exact h
  · intro i
    apply bu_time_weak_identity_of_global hKtarget
      (fun z => w z i) (fun z => Dtw z i)
      (hWzero i) (hDtzero i) _ φ hφ
    intro ψ hψ hψc
    have h := hglobal.2.2 i ψ hψ hψc
    simp_rw [hEqW i, hEqDt i] at h
    exact h

end ESS
