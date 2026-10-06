/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayAssemblyContracts
public import LeanPool.CaffarelliKohnNirenberg.Leray.PressureLimitLeray
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationPressure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Leray Pressure Prop

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem lerayPressureProp_productMeasure (T : ℝ) :
    (volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)) := by
  change ((volume : Measure (Vec3 × ℝ)).restrict
      (Set.univ ×ˢ Ioo 0 T)) = _
  rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict]
  simp

/-- The actual regularized pressure is the product-slab Riesz pressure in
`prop:leray-pressure-limit` when its two velocity factors belong to `L³`. -/
private theorem lerayPressureProp_pressure_eq_product
    (P : ParabolicPoint → ℝ) (U J : ParabolicPoint → Vec3)
    (hPcont : ContinuousOn P (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hR4 : ∀ t : ℝ, 0 < t → ∃ hF : ∀ i j : Fin 3,
      MemLp (fun x : Vec3 => J (x, t) i * U (x, t) j)
        (ENNReal.ofReal (2 : ℝ)) volume,
      (fun x : Vec3 => P (x, t)) =ᵐ[volume]
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hF i j).toLp (fun x : Vec3 => J (x, t) i * U (x, t) j)))
    (T : ℝ)
    (hU : MemLp (fun z : Vec3 × ℝ => U (parabolicHomeomorph.symm z)) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)))
    (hJ : MemLp (fun z : Vec3 × ℝ => J (parabolicHomeomorph.symm z)) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))) :
    (fun z : Vec3 × ℝ => P (parabolicHomeomorph.symm z)) =ᵐ[
      (volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)]
      lerayProductPressureOnSlab T
        (fun z => J (parabolicHomeomorph.symm z))
        (fun z => U (parabolicHomeomorph.symm z)) hJ hU := by
  classical
  let S : Set (Vec3 × ℝ) := lerayPressureLimitSlab T
  let jST : Vec3 × ℝ → Vec3 := fun z => J (parabolicHomeomorph.symm z)
  let uST : Vec3 × ℝ → Vec3 := fun z => U (parabolicHomeomorph.symm z)
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j =>
    S.indicator (fun z => jST z i * uST z j)
  let hF := rieszPressureSpaceTime_product_memLp_of_slab
    (MeasurableSet.univ.prod measurableSet_Ioo) jST uST
    (fun i => hJ.eval i) (fun j => hU.eval j)
  let q : Vec3 × ℝ → ℝ := rieszPressureSpaceTime
    (3 / 2 : ℝ) (by norm_num) F hF
  let pST : Vec3 × ℝ → ℝ := fun z => P (parabolicHomeomorph.symm z)
  let pRep : Vec3 × ℝ → ℝ := S.piecewise pST (fun _ => 0)
  have hSmeas : MeasurableSet S := by
    exact MeasurableSet.univ.prod measurableSet_Ioo
  have hMap : Set.MapsTo parabolicHomeomorph.symm S
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) := by
    intro z hz
    rcases hz with ⟨_, ht, _⟩
    exact ⟨Set.mem_univ _, ht⟩
  have hpSTcont : ContinuousOn pST S := by
    exact hPcont.comp parabolicHomeomorph.symm.continuous.continuousOn hMap
  have hpRep : Measurable pRep :=
    ContinuousOn.measurable_piecewise hpSTcont continuousOn_const hSmeas
  have hqMeas : Measurable q := by
    change Measurable (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF)
    exact rieszPressureSpaceTime_measurable (3 / 2 : ℝ) (by norm_num) F hF
  have hSlice := rieszPressureSpaceTime_slice_ae_eq
    (3 / 2 : ℝ) (by norm_num) F hF
  have hSections : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      (fun x : Vec3 => pRep (x, t)) =ᵐ[volume]
        fun x => q (x, t) := by
    filter_upwards [ae_restrict_of_ae hSlice,
      ae_restrict_mem measurableSet_Ioo] with t hSl ht
    obtain ⟨hFt, hqSlice⟩ := hSl
    obtain ⟨hF2, hP2⟩ := hR4 t ht.1
    have hF32 : ∀ i j : Fin 3,
        MemLp (fun x : Vec3 => J (x, t) i * U (x, t) j)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
      intro i j
      have h := hFt i j
      change MemLp (fun x : Vec3 =>
        S.indicator (fun z => jST z i * uST z j) (x, t))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume at h
      have hEq : (fun x : Vec3 =>
          S.indicator (fun z => jST z i * uST z j) (x, t)) =
          fun x => J (x, t) i * U (x, t) j := by
        funext x
        simp [S, jST, uST, lerayPressureLimitSlab, ht.1, ht.2]
      exact (memLp_congr_ae (Eventually.of_forall (fun x => congrFun hEq x))).1 h
    have hAgreement := rieszPressureSlice_ae_eq_of_memLp_common
      (2 : ℝ) (by norm_num) (3 / 2 : ℝ) (by norm_num)
      (fun i j x => J (x, t) i * U (x, t) j) hF2 hF32
    have hRep2 := rieszPressureSliceRepresentative_ae_eq
      (2 : ℝ) (by norm_num)
      (fun i j => (hF2 i j).toLp (fun x : Vec3 => J (x, t) i * U (x, t) j))
    have hSecInput : ∀ i j : Fin 3,
        (hFt i j).toLp (fun x : Vec3 => F i j (x, t)) =
          (hF32 i j).toLp (fun x : Vec3 => J (x, t) i * U (x, t) j) := by
      intro i j
      apply Lp.ext
      filter_upwards [(hFt i j).coeFn_toLp, (hF32 i j).coeFn_toLp]
        with x hx₁ hx₂
      rw [hx₁, hx₂]
      simp [F, S, jST, uST, lerayPressureLimitSlab, ht.1, ht.2]
    have hSliceInput :
        rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
          (fun i j => (hFt i j).toLp (fun x : Vec3 => F i j (x, t))) =
        rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
          (fun i j => (hF32 i j).toLp
            (fun x : Vec3 => J (x, t) i * U (x, t) j)) := by
      congr 1
      funext i j
      exact hSecInput i j
    have hSliceInputPoint : ∀ x : Vec3,
        (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
          (fun i j => (hFt i j).toLp (fun x : Vec3 => F i j (x, t))) : Vec3 → ℝ) x =
        (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
          (fun i j => (hF32 i j).toLp
            (fun x : Vec3 => J (x, t) i * U (x, t) j)) : Vec3 → ℝ) x := by
      intro x
      exact congrArg (fun f : Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) volume =>
        (f : Vec3 → ℝ) x) hSliceInput
    have hPpoint : (fun x : Vec3 => P (x, t)) =ᵐ[volume]
        fun x => q (x, t) := by
      filter_upwards [hP2, hRep2.symm, hAgreement, hqSlice] with x hp hr ha hq
      calc
        P (x, t) = rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
            (fun i j => (hF2 i j).toLp
              (fun y : Vec3 => J (y, t) i * U (y, t) j)) x := hp
        _ = (rieszPressureSlice (2 : ℝ) (by norm_num)
              (fun i j => (hF2 i j).toLp
                (fun y : Vec3 => J (y, t) i * U (y, t) j)) : Vec3 → ℝ) x := hr
        _ = (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
              (fun i j => (hF32 i j).toLp
                (fun y : Vec3 => J (y, t) i * U (y, t) j)) : Vec3 → ℝ) x := ha
        _ = (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
              (fun i j => (hFt i j).toLp
                (fun y : Vec3 => F i j (y, t))) : Vec3 → ℝ) x :=
          (hSliceInputPoint x).symm
        _ = q (x, t) := hq.symm
    filter_upwards [hPpoint] with x hx
    have hzt : (x, t) ∈ S := ⟨Set.mem_univ _, ⟨ht.1, ht.2⟩⟩
    simpa [pRep, pST, S, Set.piecewise, hzt] using hx
  let E : Set (Vec3 × ℝ) := {z | pRep z = q z}
  have hEmeas : MeasurableSet E := measurableSet_eq_fun hpRep hqMeas
  have hSections' : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
      ∀ᵐ x ∂(volume : Measure Vec3), (x, t) ∈ E := by
    filter_upwards [hSections] with t ht
    exact ht
  have hEswap : MeasurableSet {z : ℝ × Vec3 | (z.2, z.1) ∈ E} := by
    change MeasurableSet (Prod.swap ⁻¹' E)
    exact measurableSet_swap_iff.mpr hEmeas
  have hSwap : ∀ᵐ x ∂(volume : Measure Vec3),
      ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), (x, t) ∈ E :=
    (Measure.ae_ae_comm hEswap).mp hSections'
  have hProd : ∀ᵐ z ∂((volume : Measure Vec3).prod
      (volume.restrict (Ioo (0 : ℝ) T))), z ∈ E :=
    (Measure.ae_prod_iff_ae_ae hEmeas).2 hSwap
  have hSprod : ∀ᵐ z ∂((volume : Measure Vec3).prod
      (volume.restrict (Ioo (0 : ℝ) T))), z ∈ S := by
    have hSectionsS : ∀ᵐ x ∂(volume : Measure Vec3),
        ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), (x, t) ∈ S := by
      filter_upwards [] with x
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact ⟨Set.mem_univ _, ht⟩
    exact (Measure.ae_prod_iff_ae_ae hSmeas).2 hSectionsS
  rw [lerayPressureProp_productMeasure T]
  filter_upwards [hProd, hSprod] with z hz hzS
  have hval := hz
  change pRep z = q z at hval
  have hval' : P (parabolicHomeomorph.symm z) = q z := by
    simpa [pRep, pST, S, Set.piecewise, hzS] using hval
  change P (parabolicHomeomorph.symm z) = q z
  exact hval'

private theorem lerayPressureProp_productPressure_memLp
    (T : ℝ) (v w : Vec3 × ℝ → Vec3)
    (hv : MemLp v 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T)))
    (hw : MemLp w 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T))) :
    MemLp (lerayProductPressureOnSlab T v w hv hw)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
  change MemLp (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
      (fun i j => (lerayPressureLimitSlab T).indicator
        (fun z => v z i * w z j))
      (rieszPressureSpaceTime_product_memLp_of_slab
        (MeasurableSet.univ.prod measurableSet_Ioo) v w
        (fun i => hv.eval i) (fun j => hw.eval j)))
    (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ))
  exact rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num) _ _

private theorem lerayPressureProp_productPressure_measurable
    (T : ℝ) (v w : Vec3 × ℝ → Vec3)
    (hv : MemLp v 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T)))
    (hw : MemLp w 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T))) :
    Measurable (lerayProductPressureOnSlab T v w hv hw) := by
  change Measurable (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
      (fun i j => (lerayPressureLimitSlab T).indicator
        (fun z => v z i * w z j))
      (rieszPressureSpaceTime_product_memLp_of_slab
        (MeasurableSet.univ.prod measurableSet_Ioo) v w
        (fun i => hv.eval i) (fun j => hw.eval j)) )
  exact rieszPressureSpaceTime_measurable (3 / 2 : ℝ) (by norm_num) _ _

private theorem lerayPressureProp_productPressure_congr
    (T : ℝ) (v v' w w' : Vec3 × ℝ → Vec3)
    (hv : MemLp v 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T)))
    (hv' : MemLp v' 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T)))
    (hw : MemLp w 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T)))
    (hw' : MemLp w' 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T))) (hV : v = v') (hW : w = w') :
    lerayProductPressureOnSlab T v w hv hw =
      lerayProductPressureOnSlab T v' w' hv' hw' := by
  subst v'
  subst w'
  have hvEq : hv = hv' := Subsingleton.elim _ _
  have hwEq : hw = hw' := Subsingleton.elim _ _
  subst hv'
  subst hw'
  rfl
private theorem lerayPressureProp_productPressure_sections_agree
    (T S : ℝ) (v w : Vec3 × ℝ → Vec3)
    (hvT : MemLp v 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T)))
    (hwT : MemLp w 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T)))
    (hvS : MemLp v 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab S)))
    (hwS : MemLp w 3 ((volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab S))) :
    ∀ᵐ t ∂(volume : Measure ℝ), 0 < t → t < T → t < S →
      (fun x : Vec3 => lerayProductPressureOnSlab T v w hvT hwT (x, t)) =ᵐ[volume]
      (fun x : Vec3 => lerayProductPressureOnSlab S v w hvS hwS (x, t)) := by
  let FT : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j =>
    (lerayPressureLimitSlab T).indicator (fun z => v z i * w z j)
  let FS : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j =>
    (lerayPressureLimitSlab S).indicator (fun z => v z i * w z j)
  let hFT := rieszPressureSpaceTime_product_memLp_of_slab
    (MeasurableSet.univ.prod measurableSet_Ioo) v w
    (fun i => hvT.eval i) (fun j => hwT.eval j)
  let hFS := rieszPressureSpaceTime_product_memLp_of_slab
    (MeasurableSet.univ.prod measurableSet_Ioo) v w
    (fun i => hvS.eval i) (fun j => hwS.eval j)
  have hSliceT := rieszPressureSpaceTime_slice_ae_eq
    (3 / 2 : ℝ) (by norm_num) FT hFT
  have hSliceS := rieszPressureSpaceTime_slice_ae_eq
    (3 / 2 : ℝ) (by norm_num) FS hFS
  filter_upwards [hSliceT, hSliceS] with t hT hS
  intro ht htT htS
  rcases hT with ⟨hFt, hEqT⟩
  rcases hS with ⟨hFs, hEqS⟩
  have hInputs : ∀ i j,
      (hFt i j).toLp (fun x : Vec3 => FT i j (x, t)) =
        (hFs i j).toLp (fun x : Vec3 => FS i j (x, t)) := by
    intro i j
    apply Lp.ext
    filter_upwards [(hFt i j).coeFn_toLp, (hFs i j).coeFn_toLp]
      with x h₁ h₂
    rw [h₁, h₂]
    simp [FT, FS, lerayPressureLimitSlab, ht, htT, htS]
  have hPressure :
      rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
        (fun i j => (hFt i j).toLp (fun x : Vec3 => FT i j (x, t))) =
      rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
        (fun i j => (hFs i j).toLp (fun x : Vec3 => FS i j (x, t))) := by
    congr 1
    funext i j
    exact hInputs i j
  have hPressurePoint : ∀ x : Vec3,
      (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
        (fun i j => (hFt i j).toLp (fun x : Vec3 => FT i j (x, t))) : Vec3 → ℝ) x =
      (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
        (fun i j => (hFs i j).toLp (fun x : Vec3 => FS i j (x, t))) : Vec3 → ℝ) x := by
    intro x
    exact congrArg (fun f : Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ)) volume =>
      (f : Vec3 → ℝ) x) hPressure
  filter_upwards [hEqT, hEqS] with x hxT hxS
  calc
    lerayProductPressureOnSlab T v w hvT hwT (x, t) =
        (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
          (fun i j => (hFt i j).toLp (fun y : Vec3 => FT i j (y, t))) : Vec3 → ℝ) x := hxT
    _ = (rieszPressureSlice (3 / 2 : ℝ) (by norm_num)
          (fun i j => (hFs i j).toLp (fun y : Vec3 => FS i j (y, t))) : Vec3 → ℝ) x :=
      hPressurePoint x
    _ = lerayProductPressureOnSlab S v w hvS hwS (x, t) := hxS.symm

@[expose]
def lerayPressurePropGlue
    (q : ℕ → Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  q 0 z + ∑' n : ℕ,
    if (n + 1 : ℝ) ≤ max 0 z.2 then q (n + 1) z - q n z else 0

private theorem lerayPressureProp_sum_telescope (q : ℕ → ℝ) (k : ℕ) :
    q 0 + ∑ n ∈ Finset.range k, (q (n + 1) - q n) = q k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        q 0 + (∑ n ∈ Finset.range k, (q (n + 1) - q n) +
            (q (k + 1) - q k)) =
            (q 0 + ∑ n ∈ Finset.range k, (q (n + 1) - q n)) +
              (q (k + 1) - q k) := by ring
        _ = q k + (q (k + 1) - q k) := by rw [ih]
        _ = q (k + 1) := by ring

private theorem lerayPressureProp_glue_eq_selected
    (q : ℕ → Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) :
    lerayPressurePropGlue q z =
      q (Nat.find (exists_nat_gt (max 0 z.2)) - 1) z := by
  let H := exists_nat_gt (max 0 z.2)
  let k := Nat.find H
  have hk : max 0 z.2 < (k : ℝ) := Nat.find_spec H
  have hkpos : 0 < k := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left 0 z.2) hk)
  have hactive (n : ℕ) :
      ((n + 1 : ℝ) ≤ max 0 z.2) ↔ n + 1 < k := by
    constructor
    · intro hn
      exact_mod_cast lt_of_le_of_lt hn hk
    · intro hn
      have hnot : ¬ max 0 z.2 < (n + 1 : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using (Nat.find_min H hn)
      exact le_of_not_gt hnot
  have hsum :
      (∑' n : ℕ, if (n + 1 : ℝ) ≤ max 0 z.2 then
        q (n + 1) z - q n z else 0) =
      ∑ n ∈ Finset.range (k - 1), (q (n + 1) z - q n z) := by
    rw [tsum_eq_sum (s := Finset.range (k - 1))]
    · apply Finset.sum_congr rfl
      intro n hn
      have hn' : n < k - 1 := Finset.mem_range.mp hn
      have hn'' : n + 1 < k := by omega
      simp [(hactive n).2 hn'']
    · intro n hn
      have hn' : ¬ n < k - 1 := by
        simpa only [Finset.mem_range] using hn
      have hn'' : ¬ n + 1 < k := by omega
      simp [(hactive n).not.mpr hn'']
  dsimp [lerayPressurePropGlue]
  rw [hsum]
  simpa [k] using lerayPressureProp_sum_telescope (fun n => q n z) (k - 1)

private theorem lerayPressureProp_glue_measurable
    (q : ℕ → Vec3 × ℝ → ℝ)
    (hq : ∀ n, Measurable (q n)) : Measurable (lerayPressurePropGlue q) := by
  have hterm (n : ℕ) : Measurable (fun z : Vec3 × ℝ =>
      if (n + 1 : ℝ) ≤ max 0 z.2 then q (n + 1) z - q n z else 0) := by
    apply Measurable.ite
    · exact measurableSet_le measurable_const
        (continuous_const.max continuous_snd).measurable
    · exact (hq (n + 1)).sub (hq n)
    · exact measurable_const
  have hsummable (z : Vec3 × ℝ) : Summable (fun n : ℕ =>
      if (n + 1 : ℝ) ≤ max 0 z.2 then q (n + 1) z - q n z else 0) := by
    let H := exists_nat_gt (max 0 z.2)
    let k := Nat.find H
    have hk : max 0 z.2 < (k : ℝ) := Nat.find_spec H
    have hactive (n : ℕ) :
        ((n + 1 : ℝ) ≤ max 0 z.2) ↔ n + 1 < k := by
      constructor
      · intro hn
        exact_mod_cast lt_of_le_of_lt hn hk
      · intro hn
        have hnot : ¬ max 0 z.2 < (n + 1 : ℝ) :=
          by simpa only [Nat.cast_add, Nat.cast_one] using (Nat.find_min H hn)
        exact le_of_not_gt hnot
    apply summable_of_hasFiniteSupport
    refine (Finset.range (k - 1)).finite_toSet.subset ?_
    intro n hn
    change (if (n + 1 : ℝ) ≤ max 0 z.2 then
      q (n + 1) z - q n z else 0) ≠ 0 at hn
    have hnlt : n < k - 1 := by
      by_contra h
      have hnnot : ¬ n + 1 < k := by omega
      simp [(hactive n).not.mpr hnnot] at hn
    exact Finset.mem_range.mpr hnlt
  have hpartial (m : ℕ) : Measurable (fun z : Vec3 × ℝ =>
      q 0 z + ∑ n ∈ Finset.range m,
        (if (n + 1 : ℝ) ≤ max 0 z.2 then q (n + 1) z - q n z else 0)) := by
    exact (hq 0).add (Finset.measurable_sum (Finset.range m)
      fun n hn => hterm n)
  refine measurable_of_tendsto_metrizable hpartial ?_
  rw [tendsto_pi_nhds]
  intro z
  have hlim := (hsummable z).hasSum.tendsto_sum_nat
  simpa [lerayPressurePropGlue, add_comm, add_left_comm, add_assoc] using
    hlim.const_add (q 0 z)

private theorem lerayPressureProp_glue_pressure
    (u : Vec3 × ℝ → Vec3)
    (hu : ∀ T : ℝ, 0 < T → MemLp u 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))) :
    ∃ p : Vec3 × ℝ → ℝ, ∀ (T : ℝ) (hT : 0 < T),
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) ∧
      p =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)]
        lerayProductPressureOnSlab T u u (hu T hT) (hu T hT) := by
  classical
  let hUn (n : ℕ) : MemLp u 3
      ((volume : Measure (Vec3 × ℝ)).restrict
        (lerayPressureLimitSlab ((n : ℝ) + 1))) :=
    hu ((n : ℝ) + 1) (by positivity)
  let q (n : ℕ) : Vec3 × ℝ → ℝ :=
    lerayProductPressureOnSlab ((n : ℝ) + 1) u u (hUn n) (hUn n)
  have hqMem (n : ℕ) : MemLp (q n) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    exact lerayPressureProp_productPressure_memLp ((n : ℝ) + 1) u u
      (hUn n) (hUn n)
  have hqMeas (n : ℕ) : Measurable (q n) := by
    exact lerayPressureProp_productPressure_measurable ((n : ℝ) + 1) u u
      (hUn n) (hUn n)
  let p := lerayPressurePropGlue q
  have hpMeas : Measurable p := lerayPressureProp_glue_measurable q hqMeas
  refine ⟨p, ?_⟩
  intro T hT
  let qT := lerayProductPressureOnSlab T u u (hu T hT) (hu T hT)
  have hqTMeas : Measurable qT :=
    lerayPressureProp_productPressure_measurable T u u (hu T hT) (hu T hT)
  have hqTMem : MemLp qT (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    lerayPressureProp_productPressure_memLp T u u (hu T hT) (hu T hT)
  have hSections : ∀ n : ℕ, ∀ᵐ t ∂(volume : Measure ℝ),
      0 < t → t < ((n : ℝ) + 1) → t < T →
      (fun x : Vec3 => q n (x, t)) =ᵐ[volume]
        (fun x : Vec3 => qT (x, t)) := by
    intro n
    exact lerayPressureProp_productPressure_sections_agree
      ((n : ℝ) + 1) T u u (hUn n) (hUn n) (hu T hT) (hu T hT)
  have hSectionsAll : ∀ᵐ t ∂(volume : Measure ℝ), ∀ n : ℕ,
      0 < t → t < ((n : ℝ) + 1) → t < T →
        (fun x : Vec3 => q n (x, t)) =ᵐ[volume]
          (fun x : Vec3 => qT (x, t)) :=
    ae_all_iff.2 hSections
  have hSectionsRestr : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), ∀ n : ℕ,
      0 < t → t < ((n : ℝ) + 1) → t < T →
        (fun x : Vec3 => q n (x, t)) =ᵐ[volume]
          (fun x : Vec3 => qT (x, t)) :=
    (ae_restrict_iff' measurableSet_Ioo).2
      (hSectionsAll.mono fun _ h _ => h)
  have hpEq : p =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict
      (lerayPressureLimitSlab T)] qT := by
    let E : Set (Vec3 × ℝ) := {z | p z = qT z}
    have hEmeas : MeasurableSet E := measurableSet_eq_fun hpMeas hqTMeas
    have hSectionsEq : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)),
        ∀ᵐ x ∂(volume : Measure Vec3), (x, t) ∈ E := by
      filter_upwards [hSectionsRestr,
        ae_restrict_mem measurableSet_Ioo] with t hAll ht
      have ht0 : 0 < t := ht.1
      have htT : t < T := ht.2
      let k := Nat.find (exists_nat_gt (max 0 t))
      let n := k - 1
      have hk : max 0 t < (k : ℝ) := Nat.find_spec (exists_nat_gt (max 0 t))
      have hkpos : 0 < k := by
        exact_mod_cast (lt_of_le_of_lt (le_max_left 0 t) hk)
      have hknNat : n + 1 = k := by
        simpa [n] using Nat.succ_pred_eq_of_pos hkpos
      have hkn : ((n : ℝ) + 1) = (k : ℝ) := by exact_mod_cast hknNat
      have htn : t < ((n : ℝ) + 1) := by
        calc
          t ≤ max 0 t := le_max_right 0 t
          _ < (k : ℝ) := hk
          _ = (n : ℝ) + 1 := hkn.symm
      have hqn := hAll n ht0 htn htT
      filter_upwards [hqn] with x hx
      have hsel : p (x, t) = q n (x, t) := by
        simpa [p, n, k] using lerayPressureProp_glue_eq_selected q (x, t)
      exact hsel.trans hx
    have hEswap : MeasurableSet {z : ℝ × Vec3 | (z.2, z.1) ∈ E} := by
      change MeasurableSet (Prod.swap ⁻¹' E)
      exact measurableSet_swap_iff.mpr hEmeas
    have hSwap : ∀ᵐ x ∂(volume : Measure Vec3),
        ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), (x, t) ∈ E :=
      (Measure.ae_ae_comm hEswap).mp hSectionsEq
    have hProd : ∀ᵐ z ∂((volume : Measure Vec3).prod
        (volume.restrict (Ioo (0 : ℝ) T))), z ∈ E :=
      (Measure.ae_prod_iff_ae_ae hEmeas).2 hSwap
    rw [lerayPressureProp_productMeasure T]
    filter_upwards [hProd] with z hz
    exact hz
  have hpMem : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) := by
    exact (memLp_congr_ae hpEq).2 (hqTMem.mono_measure Measure.restrict_le_self)
  exact ⟨hpMem, hpEq⟩

/-- The regularized pressure clause and the further-subsequence `L³`
membership clause imply `prop:leray-pressure-limit` on every finite slab. -/
theorem lerayPressureProp_of_regularised_pressure_data
    (ρ : CKN.Leray.RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε),
      ContinuousOn (pε a ha ε)
          (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
      ∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3,
          MemLp (fun x : Vec3 =>
            CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                (uε a ha ε) (x, t) i * (uε a ha ε) (x, t) j)
            (ENNReal.ofReal (2 : ℝ)) volume,
          (fun x : Vec3 => pε a ha ε (x, t)) =ᵐ[volume]
            CKN.Leray.rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
              (fun i j => (hF i j).toLp (fun x : Vec3 =>
                CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                    (uε a ha ε) (x, t) i * (uε a ha ε) (x, t) j)))
    (hlerayLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (_hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (_hεseq : Tendsto εseq atTop (nhds 0)),
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ Tendsto τ atTop atTop ∧
        (∀ T : ℝ, 0 < T → ∀ n : ℕ,
          MemLp (uε a ha (εseq (τ n))) 3
            (volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))))
    : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0))
      (σ : ℕ → ℕ) (u : ParabolicPoint → Vec3)
      (hσ : StrictMono σ) (hσtop : Tendsto σ atTop atTop)
      (hεsubseq : Tendsto (fun n => εseq (σ n)) atTop (nhds 0))
      (hUseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (uε a ha (εseq (σ n)) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0))
      (hJseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
            (by exact (hseq (σ n)).1)
            (uε a ha (εseq (σ n))) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0)),
      ∃ p : ParabolicPoint → ℝ,
        ∀ T : ℝ, 0 < T →
          let μ : Measure (Vec3 × ℝ) :=
            (volume : Measure (Vec3 × ℝ)).restrict
              (CKN.Leray.lerayPressureLimitSlab T)
          let uST : Vec3 × ℝ → Vec3 :=
            fun z => u (parabolicHomeomorph.symm z)
          let pST : Vec3 × ℝ → ℝ :=
            fun z => p (parabolicHomeomorph.symm z)
          let pseq : ℕ → Vec3 × ℝ → ℝ := fun n z =>
            pε a ha (εseq (σ n)) (parabolicHomeomorph.symm z)
          ∃ hu : MemLp uST 3 μ,
            MemLp pST (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
            pST =ᵐ[μ] CKN.Leray.lerayProductPressureOnSlab T uST uST hu hu ∧
            Tendsto (fun n => eLpNorm (pseq n - pST)
              (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0) := by
  intro a ha εseq hseq hεseq σ u hσ hσtop hεsubseq hUseqLthree hJseqLthree
  let εsub : ℕ → ℝ := fun n => εseq (σ n)
  have hseqSub : ∀ n, 0 < εsub n ∧ εsub n ≤ 1 := fun n => hseq (σ n)
  rcases hlerayLimit a ha εsub hseqSub hεsubseq with
    ⟨τ, hτstrict, hτtop, hUthree⟩
  let uST : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  have huPar (T : ℝ) (hT : 0 < T) :
      MemLp u 3 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    have hUsub : ∀ n : ℕ,
        MemLp (uε a ha (εsub (τ n))) 3
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
      hUthree T hT
    have hconv : Tendsto
        (fun n => eLpNorm (uε a ha (εsub (τ n)) - u)
          (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
        atTop (nhds 0) := by
      simpa only [Function.comp_def, εsub] using
        (hUseqLthree T hT).comp hτtop
    have hconv3 : Tendsto
        (fun n => eLpNorm (uε a ha (εsub (τ n)) - u) 3
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
        atTop (nhds 0) := by
      simpa only [h3] using hconv
    exact Lp.memLp_of_cauchy_tendsto (by norm_num) hUsub u hconv3
  have huProduct (T : ℝ) (hT : 0 < T) :
      MemLp uST 3 ((volume : Measure (Vec3 × ℝ)).restrict
        (lerayPressureLimitSlab T)) := by
    have hSmeas : MeasurableSet
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
      MeasurableSet.univ.prod measurableSet_Ioo
    have hpre : parabolicHomeomorph.symm ⁻¹'
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) =
          lerayPressureLimitSlab T := by
      ext z
      rfl
    have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
    rw [hpre] at hmp
    exact (huPar T hT).comp_measurePreserving hmp
  obtain ⟨pST, hpGlue⟩ := lerayPressureProp_glue_pressure uST huProduct
  let p : ParabolicPoint → ℝ := fun z => pST (parabolicHomeomorph z)
  refine ⟨p, ?_⟩
  intro T hT
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)
  let μPar : Measure ParabolicPoint := volume.restrict
    (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  let Upar : ℕ → ParabolicPoint → Vec3 :=
    fun n => uε a ha (εseq (σ n))
  let Jpar : ℕ → ParabolicPoint → Vec3 := fun n =>
    CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
      (by exact (hseq (σ n)).1) (Upar n)
  let Uprod : ℕ → Vec3 × ℝ → Vec3 :=
    fun n z => Upar n (parabolicHomeomorph.symm z)
  let Jprod : ℕ → Vec3 × ℝ → Vec3 :=
    fun n z => Jpar n (parabolicHomeomorph.symm z)
  have hSmeas : MeasurableSet
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph.symm ⁻¹'
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) =
        lerayPressureLimitSlab T := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
  rw [hpre] at hmp
  have huParT : MemLp u 3 μPar := huPar T hT
  have huProdT : MemLp uST 3 μ := by
    change MemLp (u ∘ parabolicHomeomorph.symm) 3 μ
    exact huParT.comp_measurePreserving hmp
  have hUconvPar : Tendsto (fun n => eLpNorm (Upar n - u)
      (ENNReal.ofReal (3 : ℝ)) μPar) atTop (nhds 0) := by
    simpa [Upar, μPar] using hUseqLthree T hT
  have hJconvPar : Tendsto (fun n => eLpNorm (Jpar n - u)
      (ENNReal.ofReal (3 : ℝ)) μPar) atTop (nhds 0) := by
    simpa [Jpar, Upar, μPar] using hJseqLthree T hT
  have hUmemPar : ∀ᶠ n : ℕ in atTop, MemLp (Upar n) 3 μPar := by
    have hfinite : ∀ᶠ n : ℕ in atTop,
        eLpNorm (Upar n - u) (ENNReal.ofReal (3 : ℝ)) μPar < ∞ :=
      hUconvPar.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
    filter_upwards [hfinite] with n hn
    have hdiff : MemLp (Upar n - u) 3 μPar := by
      rw [memLp_iff]
      simpa only [h3] using hn
    have hadd := hdiff.add huParT
    apply (memLp_congr_ae (Filter.Eventually.of_forall fun z => ?_)).1 hadd
    simp [Pi.sub_apply]
  have hJmemPar : ∀ᶠ n : ℕ in atTop, MemLp (Jpar n) 3 μPar := by
    have hfinite : ∀ᶠ n : ℕ in atTop,
        eLpNorm (Jpar n - u) (ENNReal.ofReal (3 : ℝ)) μPar < ∞ :=
      hJconvPar.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
    filter_upwards [hfinite] with n hn
    have hdiff : MemLp (Jpar n - u) 3 μPar := by
      rw [memLp_iff]
      simpa only [h3] using hn
    have hadd := hdiff.add huParT
    apply (memLp_congr_ae (Filter.Eventually.of_forall fun z => ?_)).1 hadd
    simp [Pi.sub_apply]
  have hUmem : ∀ᶠ n : ℕ in atTop, MemLp (Uprod n) 3 μ := by
    filter_upwards [hUmemPar] with n hn
    change MemLp (Upar n ∘ parabolicHomeomorph.symm) 3 μ
    exact hn.comp_measurePreserving hmp
  have hJmem : ∀ᶠ n : ℕ in atTop, MemLp (Jprod n) 3 μ := by
    filter_upwards [hJmemPar] with n hn
    change MemLp (Jpar n ∘ parabolicHomeomorph.symm) 3 μ
    exact hn.comp_measurePreserving hmp
  have hUeq (n : ℕ) (hn : MemLp (Upar n) 3 μPar) :
      eLpNorm (Uprod n - uST) (ENNReal.ofReal (3 : ℝ)) μ =
        eLpNorm (Upar n - u) (ENNReal.ofReal (3 : ℝ)) μPar := by
    have hdiff := hn.sub huParT
    have h := eLpNorm_comp_measurePreserving
      (p := ENNReal.ofReal (3 : ℝ)) hdiff.aestronglyMeasurable hmp
    have heq : Uprod n - uST = (Upar n - u) ∘ parabolicHomeomorph.symm := by
      funext z
      rfl
    rw [heq]
    exact h
  have hJeq (n : ℕ) (hn : MemLp (Jpar n) 3 μPar) :
      eLpNorm (Jprod n - uST) (ENNReal.ofReal (3 : ℝ)) μ =
        eLpNorm (Jpar n - u) (ENNReal.ofReal (3 : ℝ)) μPar := by
    have hdiff := hn.sub huParT
    have h := eLpNorm_comp_measurePreserving
      (p := ENNReal.ofReal (3 : ℝ)) hdiff.aestronglyMeasurable hmp
    have heq : Jprod n - uST = (Jpar n - u) ∘ parabolicHomeomorph.symm := by
      funext z
      rfl
    rw [heq]
    exact h
  have hUconv : Tendsto (fun n => eLpNorm (Uprod n - uST)
      (ENNReal.ofReal (3 : ℝ)) μ) atTop (nhds 0) := by
    apply (hUseqLthree T hT).congr'
    filter_upwards [hUmemPar] with n hn
    simpa [Upar, μPar] using (hUeq n hn).symm
  have hJconv : Tendsto (fun n => eLpNorm (Jprod n - uST)
      (ENNReal.ofReal (3 : ℝ)) μ) atTop (nhds 0) := by
    apply (hJseqLthree T hT).congr'
    filter_upwards [hJmemPar] with n hn
    simpa [Jpar, μPar] using (hJeq n hn).symm
  obtain ⟨NU, hNU⟩ := Filter.eventually_atTop.1 hUmem
  obtain ⟨NJ, hNJ⟩ := Filter.eventually_atTop.1 hJmem
  let N : ℕ := max NU NJ
  let Umod : ℕ → Vec3 × ℝ → Vec3 := fun n => if n < N then uST else Uprod n
  let Jmod : ℕ → Vec3 × ℝ → Vec3 := fun n => if n < N then uST else Jprod n
  have hUmod : ∀ n : ℕ, MemLp (Umod n) 3 μ := by
    intro n
    by_cases hn : n < N
    · simp [Umod, hn]
      exact huProdT
    · have hnN : N ≤ n := le_of_not_gt hn
      have hnU : NU ≤ n := le_trans (le_max_left NU NJ) hnN
      simpa [Umod, hn] using hNU n hnU
  have hJmod : ∀ n : ℕ, MemLp (Jmod n) 3 μ := by
    intro n
    by_cases hn : n < N
    · simp [Jmod, hn]
      exact huProdT
    · have hnN : N ≤ n := le_of_not_gt hn
      have hnJ : NJ ≤ n := le_trans (le_max_right NU NJ) hnN
      simpa [Jmod, hn] using hNJ n hnJ
  have hUconvMod : Tendsto (fun n => eLpNorm (Umod n - uST)
      (ENNReal.ofReal (3 : ℝ)) μ) atTop (nhds 0) := by
    apply hUconv.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    simp [Umod, not_lt_of_ge hn]
  have hJconvMod : Tendsto (fun n => eLpNorm (Jmod n - uST)
      (ENNReal.ofReal (3 : ℝ)) μ) atTop (nhds 0) := by
    apply hJconv.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    simp [Jmod, not_lt_of_ge hn]
  have hJconv3 : Tendsto (fun n => eLpNorm (Jmod n - uST) 3 μ) atTop (nhds 0) :=
    by simpa only [h3] using hJconvMod
  have hUconv3 : Tendsto (fun n => eLpNorm (Umod n - uST) 3 μ) atTop (nhds 0) :=
    by simpa only [h3] using hUconvMod
  have hcanonical := lerayPressureLimit_Lthree T Jmod Umod uST hJmod hUmod
    huProdT hJconv3 hUconv3
  rcases hpGlue T hT with ⟨hpSTmem, hpSTeq⟩
  have hpressureEq (n : ℕ) (hn : N ≤ n) :
      pε a ha (εseq (σ n)) ∘ parabolicHomeomorph.symm =ᵐ[μ]
        lerayProductPressureOnSlab T (Jmod n) (Umod n) (hJmod n) (hUmod n) := by
    have hnU : NU ≤ n := le_trans (le_max_left NU NJ) hn
    have hnJ : NJ ≤ n := le_trans (le_max_right NU NJ) hn
    have hRdata := hregularised a ha (εseq (σ n)) (hseq (σ n)).1
    rcases hRdata with ⟨hPcont, hR4⟩
    have hU : MemLp (Uprod n) 3 μ := hNU n hnU
    have hJ : MemLp (Jprod n) 3 μ := hNJ n hnJ
    have hactual := lerayPressureProp_pressure_eq_product
      (pε a ha (εseq (σ n))) (Upar n) (Jpar n) hPcont hR4 T hU hJ
    have hmod : lerayProductPressureOnSlab T (Jprod n) (Uprod n) hJ hU =
        lerayProductPressureOnSlab T (Jmod n) (Umod n) (hJmod n) (hUmod n) := by
      have hJval : Jmod n = Jprod n := by
        simp [Jmod, show ¬ n < N from not_lt_of_ge hn]
      have hUval : Umod n = Uprod n := by
        simp [Umod, show ¬ n < N from not_lt_of_ge hn]
      exact lerayPressureProp_productPressure_congr T
        (Jprod n) (Jmod n) (Uprod n) (Umod n) hJ (hJmod n) hU (hUmod n)
        hJval.symm hUval.symm
    filter_upwards [hactual] with z hzP
    exact hzP.trans (congrFun hmod z)
  have hnormEq (n : ℕ) (hn : N ≤ n) :
      eLpNorm
          (fun z : Vec3 × ℝ =>
            pε a ha (εseq (σ n)) (parabolicHomeomorph.symm z) - pST z)
          (ENNReal.ofReal (3 / 2 : ℝ)) μ =
        eLpNorm
          (lerayProductPressureOnSlab T (Jmod n) (Umod n) (hJmod n) (hUmod n) -
            lerayProductPressureOnSlab T uST uST huProdT huProdT)
          (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply eLpNorm_congr_ae
    filter_upwards [hpressureEq n hn, hpSTeq] with z hzP hzST
    have hzP' : pε a ha (εseq (σ n)) (parabolicHomeomorph.symm z) =
        lerayProductPressureOnSlab T (Jmod n) (Umod n) (hJmod n) (hUmod n) z := by
      simpa only [Function.comp_apply] using hzP
    simp only [hzP', hzST, Pi.sub_apply]
  have hpressureConv : Tendsto
      (fun n => eLpNorm
        (fun z : Vec3 × ℝ =>
          pε a ha (εseq (σ n)) (parabolicHomeomorph.symm z) - pST z)
        (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0) := by
    apply hcanonical.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    exact (hnormEq n hn).symm
  refine ⟨?_, ?_, ?_, hpressureConv⟩
  · simpa [uST, μ] using huProdT
  · simpa [p] using hpSTmem
  · simpa [p, uST, μ] using hpSTeq

end CKN.Leray

end
