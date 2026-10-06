/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressureDualityCompact

/-!
# Unrestricted space-time Riesz duality

The compact-core pairing extends to arbitrary dual `L^r` classes by
continuity and density.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem rieszPressureComponent_pairing_core
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q)
    (hHolder : r.HolderConjugate q) (i j : Fin 3)
    (u : rieszPressureSpaceTimeCore r hr)
    (v : rieszPressureSpaceTimeCore q hq) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hq.le⟩
    ∫ z, (rieszPressureSpaceTimeComponent r hr i j (u : _ ) :
      Vec3 × ℝ → ℝ) z * (v : Lp ℝ (ENNReal.ofReal q)
        (volume : Measure (Vec3 × ℝ))) z =
    ∫ z, (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) z *
      (rieszPressureSpaceTimeComponent q hq j i (v : _) :
        Vec3 × ℝ → ℝ) z := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  rcases u.property with ⟨F, hFu⟩
  rcases v.property with ⟨G, hGv⟩
  have hFmem : MemLp F.value (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    F.continuous_value.memLp_of_hasCompactSupport F.compact_support_value
  have hGmem : MemLp G.value (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ)) :=
    G.continuous_value.memLp_of_hasCompactSupport G.compact_support_value
  have hFinput : rieszPressureCompactInputLpClass r hr F = hFmem.toLp F.value := rfl
  have hGinput : rieszPressureCompactInputLpClass q hq G = hGmem.toLp G.value := rfl
  have hu : (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) =
      hFmem.toLp F.value := hFu.trans hFinput
  have hv : (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) =
      hGmem.toLp G.value := hGv.trans hGinput
  have hTu : rieszPressureSpaceTimeComponent r hr i j
      (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) =
      rieszPressureComponentCompactClass r hr i j (F := F.value)
        F.continuous_value F.compact_support_value := by
    rw [hu]
    exact rieszPressureSpaceTimeComponent_eq_compact r hr i j
      F.continuous_value F.compact_support_value
  have hTv : rieszPressureSpaceTimeComponent q hq j i
      (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) =
      rieszPressureComponentCompactClass q hq j i (F := G.value)
        G.continuous_value G.compact_support_value := by
    rw [hv]
    exact rieszPressureSpaceTimeComponent_eq_compact q hq j i
      G.continuous_value G.compact_support_value
  have huF : ((u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
      Vec3 × ℝ → ℝ) =ᵐ[volume] F.value := by
    filter_upwards [(Lp.ext_iff).1 hu, hFmem.coeFn_toLp] with z hzu hFz
    exact hzu.trans hFz
  have hvG : ((v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
      Vec3 × ℝ → ℝ) =ᵐ[volume] G.value := by
    filter_upwards [(Lp.ext_iff).1 hv, hGmem.coeFn_toLp] with z hzv hGz
    exact hzv.trans hGz
  have hTuAE : (rieszPressureSpaceTimeComponent r hr i j
      (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :
      Vec3 × ℝ → ℝ) =ᵐ[volume]
      (@rieszPressureComponentCompactClass r hr i j F.value
        F.continuous_value F.compact_support_value : Vec3 × ℝ → ℝ) :=
    (Lp.ext_iff).1 hTu
  have hTvAE : (rieszPressureSpaceTimeComponent q hq j i
      (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
      Vec3 × ℝ → ℝ) =ᵐ[volume]
      (@rieszPressureComponentCompactClass q hq j i G.value
        G.continuous_value G.compact_support_value : Vec3 × ℝ → ℝ) :=
    (Lp.ext_iff).1 hTv
  have hcompact := rieszPressureComponentCompactClass_pairing r hr q hq hHolder i j
    F.continuous_value F.compact_support_value G.continuous_value G.compact_support_value
  calc
    ∫ z, (rieszPressureSpaceTimeComponent r hr i j (u : _) :
        Vec3 × ℝ → ℝ) z * (v : Lp ℝ (ENNReal.ofReal q)
          (volume : Measure (Vec3 × ℝ))) z =
        ∫ z, (@rieszPressureComponentCompactClass r hr i j F.value
          F.continuous_value F.compact_support_value : Vec3 × ℝ → ℝ) z * G.value z := by
            apply integral_congr_ae
            filter_upwards [hTuAE, hvG] with z hTz hvz
            rw [hTz, hvz]
    _ = ∫ z, F.value z * (@rieszPressureComponentCompactClass q hq j i G.value
          G.continuous_value G.compact_support_value :
          Vec3 × ℝ → ℝ) z := hcompact
    _ = ∫ z, (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) z *
          (rieszPressureSpaceTimeComponent q hq j i (v : _) :
            Vec3 × ℝ → ℝ) z := by
            apply integral_congr_ae
            filter_upwards [huF, hTvAE] with z huz hTz
            rw [huz, hTz]

private theorem rieszPressureComponent_pairing_right_core
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q)
    (hHolder : r.HolderConjugate q) (i j : Fin 3)
    (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)))
    (v : rieszPressureSpaceTimeCore q hq) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hq.le⟩
    ∫ z, (rieszPressureSpaceTimeComponent r hr i j u : Vec3 × ℝ → ℝ) z *
      (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) z =
    ∫ z, (u : Vec3 × ℝ → ℝ) z *
      (rieszPressureSpaceTimeComponent q hq j i (v : _) : Vec3 × ℝ → ℝ) z := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  let T_r := rieszPressureSpaceTimeComponent r hr i j
  let T_q := rieszPressureSpaceTimeComponent q hq j i
  let A : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) →L[ℝ] ℝ :=
    (rieszPressureLpPairingCLM r hr q hq hHolder (v : _)).comp T_r
  let B : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) →L[ℝ] ℝ :=
    rieszPressureLpPairingCLM r hr q hq hHolder (T_q (v : _))
  have hClosed : IsClosed {w | A w = B w} := isClosed_eq A.continuous B.continuous
  have hEq : A u = B u := by
    apply isClosed_property
      (denseRange_subtype_val.mpr (rieszPressureSpaceTimeCore_dense r hr)) hClosed
    rintro ⟨w, hw⟩
    have hcore := rieszPressureComponent_pairing_core r hr q hq hHolder i j
      ⟨w, hw⟩ v
    change (∫ z, ((T_r w : Lp ℝ (ENNReal.ofReal r)
        (volume : Measure (Vec3 × ℝ))) : Vec3 × ℝ → ℝ) z *
        ((v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
          Vec3 × ℝ → ℝ) z) =
      (∫ z, (w : Vec3 × ℝ → ℝ) z *
        ((T_q (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ)))) :
          Vec3 × ℝ → ℝ) z) at hcore
    change A w = B w
    exact hcore
  change (∫ z, ((T_r u : Lp ℝ (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ))) : Vec3 × ℝ → ℝ) z *
      ((v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
        Vec3 × ℝ → ℝ) z) =
    (∫ z, (u : Vec3 × ℝ → ℝ) z *
      ((T_q (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
        Vec3 × ℝ → ℝ) z))
  exact hEq

/-- The component adjoint identity holds for every space-time `L^r` input,
used by `lem:riesz-duality`. -/
theorem rieszPressureSpaceTimeComponent_duality
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q)
    (hHolder : r.HolderConjugate q) (i j : Fin 3)
    (u : Lp ℝ (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)))
    (v : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hq.le⟩
    ∫ z, (rieszPressureSpaceTimeComponent r hr i j u :
        Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z =
      ∫ z, (u : Vec3 × ℝ → ℝ) z *
        (rieszPressureSpaceTimeComponent q hq j i v : Vec3 × ℝ → ℝ) z := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  have hHolderSymm : q.HolderConjugate r := hHolder.symm
  let T_r := rieszPressureSpaceTimeComponent r hr i j
  let T_q := rieszPressureSpaceTimeComponent q hq j i
  let A : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ)) →L[ℝ] ℝ :=
    rieszPressureLpPairingCLM q hq r hr hHolderSymm (T_r u)
  let B : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ)) →L[ℝ] ℝ :=
    (rieszPressureLpPairingCLM q hq r hr hHolderSymm u).comp T_q
  have hClosed : IsClosed {w | A w = B w} := isClosed_eq A.continuous B.continuous
  have hOnCore : ∀ w : rieszPressureSpaceTimeCore q hq, A w = B w := by
    intro w
    have hcore := rieszPressureComponent_pairing_right_core
      r hr q hq hHolder i j u w
    calc
      A w = ∫ z, (w : Lp ℝ (ENNReal.ofReal q)
          (volume : Measure (Vec3 × ℝ))) z *
          (T_r u : Vec3 × ℝ → ℝ) z := by
            dsimp [A]
            exact rieszPressureLpPairingCLM_apply q hq r hr hHolderSymm (T_r u) w
      _ = ∫ z, (T_r u : Vec3 × ℝ → ℝ) z *
          (w : Lp ℝ (ENNReal.ofReal q)
            (volume : Measure (Vec3 × ℝ))) z := by
            apply integral_congr_ae
            filter_upwards [] with z
            ring
      _ = ∫ z, (u : Vec3 × ℝ → ℝ) z *
          (T_q (w : Lp ℝ (ENNReal.ofReal q)
            (volume : Measure (Vec3 × ℝ))) : Vec3 × ℝ → ℝ) z := hcore
      _ = ∫ z, (T_q (w : Lp ℝ (ENNReal.ofReal q)
          (volume : Measure (Vec3 × ℝ))) : Vec3 × ℝ → ℝ) z *
          (u : Vec3 × ℝ → ℝ) z := by
            apply integral_congr_ae
            filter_upwards [] with z
            ring
      _ = B w := by
            dsimp [B]
            exact (rieszPressureLpPairingCLM_apply q hq r hr hHolderSymm u
              (T_q (w : Lp ℝ (ENNReal.ofReal q)
                (volume : Measure (Vec3 × ℝ)))))
  have hEq : A v = B v := by
    apply isClosed_property
      (denseRange_subtype_val.mpr (rieszPressureSpaceTimeCore_dense q hq)) hClosed
    rintro ⟨w, hw⟩
    exact hOnCore ⟨w, hw⟩
  calc
    ∫ z, (T_r u : Vec3 × ℝ → ℝ) z * (v : Vec3 × ℝ → ℝ) z =
        ∫ z, (v : Vec3 × ℝ → ℝ) z * (T_r u : Vec3 × ℝ → ℝ) z := by
          apply integral_congr_ae
          filter_upwards [] with z
          ring
    _ = A v := by
          dsimp [A]
          exact (rieszPressureLpPairingCLM_apply q hq r hr hHolderSymm (T_r u) v).symm
    _ = B v := hEq
    _ = ∫ z, (T_q v : Vec3 × ℝ → ℝ) z * (u : Vec3 × ℝ → ℝ) z := by
          dsimp [B]
          exact rieszPressureLpPairingCLM_apply q hq r hr hHolderSymm u (T_q v)
    _ = ∫ z, (u : Vec3 × ℝ → ℝ) z * (T_q v : Vec3 × ℝ → ℝ) z := by
          apply integral_congr_ae
          filter_upwards [] with z
          ring

/-- The nine pressure components satisfy the unrestricted tensor duality in
`lem:riesz-duality`. -/
theorem rieszPressureSpaceTimeClass_duality
    (r : ℝ) (hr : 1 < r) (q : ℝ) (hq : 1 < q)
    (hHolder : r.HolderConjugate q)
    (F : RieszPressureSpaceTimeTensorLp r)
    (g : Lp ℝ (ENNReal.ofReal q) (volume : Measure (Vec3 × ℝ))) :
    letI : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hq.le⟩
    ∫ z, (rieszPressureSpaceTimeClass r hr F : Vec3 × ℝ → ℝ) z *
        (g : Vec3 × ℝ → ℝ) z =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ z, (F i j : Vec3 × ℝ → ℝ) z *
        (rieszPressureSpaceTimeComponent q hq j i g : Vec3 × ℝ → ℝ) z := by
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  let Pair := rieszPressureLpPairingCLM r hr q hq hHolder g
  have hEntry (i j : Fin 3) :
      Pair (rieszPressureSpaceTimeComponent r hr i j (F i j)) =
        ∫ z, (F i j : Vec3 × ℝ → ℝ) z *
          (rieszPressureSpaceTimeComponent q hq j i g : Vec3 × ℝ → ℝ) z := by
    dsimp [Pair]
    exact rieszPressureSpaceTimeComponent_duality r hr q hq hHolder i j
      (F i j) g
  calc
    ∫ z, (rieszPressureSpaceTimeClass r hr F : Vec3 × ℝ → ℝ) z *
        (g : Vec3 × ℝ → ℝ) z = Pair (rieszPressureSpaceTimeClass r hr F) := by
          symm
          exact rieszPressureLpPairingCLM_apply r hr q hq hHolder g
            (rieszPressureSpaceTimeClass r hr F)
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          Pair (rieszPressureSpaceTimeComponent r hr i j (F i j)) := by
          dsimp [Pair, rieszPressureSpaceTimeClass]
          simp only [map_sum]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ z, (F i j : Vec3 × ℝ → ℝ) z *
          (rieszPressureSpaceTimeComponent q hq j i g : Vec3 × ℝ → ℝ) z := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hEntry i j

end CKN.Leray

end
