/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# Scalar chain-rule consequences for the strong `H¹` estimate

An ordered interval identity with an integrable density gives absolute
continuity and the corresponding almost-everywhere derivative
(`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set
open scoped ENNReal Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The scalar contraction of the time derivative with the vector Laplacian
is integrable in time when both spacetime fields are square integrable
(`lem:lps-H1-estimate`). -/
theorem lps_h1_chain_density_integrable
    {a b : ℝ} {Dtu : ParabolicPoint → Vec3}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    (hDtu : MemLp Dtu 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo a b))))
    (hD2u : MemLp D2u 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo a b)))) :
    MemLp (fun z : ParabolicPoint =>
      ∑ i : Fin 3, Dtu z i * (∑ j : Fin 3, D2u z i j j)) 1
        (volume.restrict (spaceTimeSet Set.univ (Ioo a b))) ∧
    IntegrableOn
      (fun t : ℝ => ∫ x : Vec3,
        ∑ i : Fin 3, Dtu (x, t) i *
          (∑ j : Fin 3, D2u (x, t) i j j))
      (Ioo a b) volume ∧
    Integrable
      (fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, Dtu (parabolicHomeomorph.symm z) i *
          (∑ j : Fin 3, D2u (parabolicHomeomorph.symm z) i j j))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo a b))
  have hSmeas : MeasurableSet
      (spaceTimeSet Set.univ (Ioo a b)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph.symm ⁻¹'
      spaceTimeSet Set.univ (Ioo a b) =
        (Set.univ : Set Vec3) ×ˢ Ioo a b := by
    ext z
    rfl
  have hmp := CKN.parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
  rw [hpre] at hmp
  have hProdSmeas : MeasurableSet
      ((Set.univ : Set Vec3) ×ˢ Ioo a b) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpreForward : parabolicHomeomorph ⁻¹'
      ((Set.univ : Set Vec3) ×ˢ Ioo a b) =
        spaceTimeSet Set.univ (Ioo a b) := by
    ext z
    rfl
  have hmap := CKN.parabolicHomeomorph_measurePreserving.restrict_preimage hProdSmeas
  rw [hpreForward] at hmap
  have hslab :
      (volume.restrict (spaceTimeSet Set.univ (Ioo a b)) :
        Measure (Vec3 × ℝ)) = μ := by
    show (volume : Measure (Vec3 × ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioo a b) = μ
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hprodSlab :
      (volume : Measure (Vec3 × ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioo a b) = μ := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hDtuProdRaw : MemLp
      (fun z : Vec3 × ℝ => Dtu (parabolicHomeomorph.symm z)) 2
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) :=
    hDtu.comp_measurePreserving hmp
  have hDtuProd : MemLp
      (fun z : Vec3 × ℝ => Dtu (parabolicHomeomorph.symm z)) 2 μ := by
    rw [← hslab]
    exact hDtuProdRaw
  have hD2uProdRaw : MemLp
      (fun z : Vec3 × ℝ => D2u (parabolicHomeomorph.symm z)) 2
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) :=
    hD2u.comp_measurePreserving hmp
  have hD2uProd : MemLp
      (fun z : Vec3 × ℝ => D2u (parabolicHomeomorph.symm z)) 2 μ := by
    rw [← hslab]
    exact hD2uProdRaw
  let lapProd : Vec3 × ℝ → Vec3 := fun z i =>
    ∑ j : Fin 3, D2u (parabolicHomeomorph.symm z) i j j
  have hlapProd : MemLp lapProd 2 μ := by
    apply memLp_pi_iff.mpr
    intro i
    apply memLp_finsetSum Finset.univ
    intro j hj
    exact (((hD2uProd.eval i).eval j).eval j)
  let q : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3,
      Dtu (parabolicHomeomorph.symm z) i * lapProd z i
  have hq : MemLp q 1 μ := by
    have hHolder : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
      ENNReal.HolderConjugate.instTwoTwo
    apply memLp_finsetSum Finset.univ
    intro i hi
    exact (hDtuProd.eval i).mul (hlapProd.eval i) (hpqr := hHolder)
  have hqInt : Integrable q μ := by
    exact memLp_one_iff_integrable.mp hq
  have hqRaw : MemLp q 1
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) := by
    rw [hprodSlab]
    exact hq
  have hqParabolic : MemLp
      (fun z : ParabolicPoint => q (parabolicHomeomorph z)) 1
      (volume.restrict (spaceTimeSet Set.univ (Ioo a b))) :=
    hqRaw.comp_measurePreserving hmap
  have hqEq :
      (fun z : ParabolicPoint => q (parabolicHomeomorph z)) =ᵐ[
          volume.restrict (spaceTimeSet Set.univ (Ioo a b))]
        (fun z => ∑ i : Fin 3, Dtu z i * (∑ j : Fin 3, D2u z i j j)) := by
    filter_upwards [ae_restrict_mem hSmeas] with z hz
    cases z with
    | mk x t => rfl
  have hpair : MemLp
      (fun z : ParabolicPoint =>
        ∑ i : Fin 3, Dtu z i * (∑ j : Fin 3, D2u z i j j)) 1
        (volume.restrict (spaceTimeSet Set.univ (Ioo a b))) := by
    exact (memLp_congr_ae hqEq).mp hqParabolic
  have hgInt : Integrable
      (fun t : ℝ => ∫ x : Vec3, q (x, t) ∂volume)
      (volume.restrict (Ioo a b)) := hqInt.integral_prod_right
  have hqForm (t : ℝ) :
    (fun x : Vec3 => q (x, t)) = fun x =>
        ∑ i : Fin 3,
          Dtu (parabolicHomeomorph.symm (x, t)) i *
            (∑ j : Fin 3,
              D2u (parabolicHomeomorph.symm (x, t)) i j j) := by
    funext x
    simp [q, lapProd]
  refine ⟨hpair, hgInt.congr ?_, hqInt⟩
  filter_upwards [] with t
  rw [hqForm t]
  simp [parabolicHomeomorph_symm_apply]

/-- Product Fubini identifies the strong-solution chain density on any
subinterval with the interval integral of its spatial slice integral
(`lem:lps-H1-estimate`). -/
theorem lps_h1_chain_setIntegral_eq_intervalIntegral
    {a b s t : ℝ} {q : Vec3 × ℝ → ℝ}
    (hq : Integrable q
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    (∫ z in spaceTimeSet Set.univ (Ioo s t),
      q (parabolicHomeomorph z)) =
      ∫ r in s..t, ∫ x : Vec3, q (x, r) := by
  have hsub : Ioo s t ⊆ Ioo a b := by
    intro r hr
    exact ⟨hs.1.trans_lt hr.1, hr.2.trans_le ht.2⟩
  have hprodSub :
      (Set.univ : Set Vec3) ×ˢ Ioo s t ⊆
        (Set.univ : Set Vec3) ×ˢ Ioo a b := Set.prod_mono subset_rfl hsub
  have hbase :
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) :
      Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) := by
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict,
      Measure.restrict_univ]
  have hqst : Integrable q
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo s t)) :=
    hq.mono_measure
      ((Measure.restrict_mono_set volume hprodSub).trans_eq hbase)
  have hmeasure :
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo s t) :
        Measure (Vec3 × ℝ)) =
      (volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict (Ioo s t)) := by
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict,
      Measure.restrict_univ]
  have hqprod : Integrable q
      ((volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict (Ioo s t))) := by
    rw [← hmeasure]
    exact hqst
  have hprod :
      (∫ z in (Set.univ : Set Vec3) ×ˢ Ioo s t, q z ∂volume) =
        ∫ r in Ioo s t, ∫ x : Vec3, q (x, r) := by
    calc
      (∫ z in (Set.univ : Set Vec3) ×ˢ Ioo s t, q z ∂volume) =
          ∫ z, q z ∂(volume.restrict
            ((Set.univ : Set Vec3) ×ˢ Ioo s t)) := rfl
      _ = ∫ r in Ioo s t, ∫ x : Vec3, q (x, r) := by
        rw [hmeasure, integral_prod_symm q hqprod]
        simp only [Measure.restrict_univ]
  have hcoordinates := CKN.setIntegral_parabolic_to_product
    (Ω := (Set.univ : Set Vec3)) (I := Ioo s t)
    (F := fun z : ParabolicPoint => q (parabolicHomeomorph z))
  rw [hcoordinates]
  simp only [parabolicHomeomorph.apply_symm_apply]
  rw [hprod]
  rw [intervalIntegral.integral_of_le hst, integral_Ioc_eq_integral_Ioo]

/-- An ordered-interval integral identity identifies the derivative of the
energy almost everywhere (`lem:lps-H1-estimate`). -/
theorem lps_ac_of_ordered_interval_integral
    {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Icc a b) volume)
    (hfg : ∀ s t, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      f t = f s + ∫ r in s..t, g r) :
    AbsolutelyContinuousOnInterval f a b ∧
      ∀ᵐ t ∂(volume.restrict (Icc a b)), deriv f t = g t := by
  let F : ℝ → ℝ := fun t => ∫ r in a..t, g r
  have hgInt : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hg
  have hFac : AbsolutelyContinuousOnInterval F a b := by
    simpa [F] using hgInt.absolutelyContinuousOnInterval_intervalIntegral
      (c := a) (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b := by
    unfold AbsolutelyContinuousOnInterval
    simp only [dist_self, Finset.sum_const_zero]
    exact tendsto_const_nhds
  have hbase := hconst.add hFac
  have hEq : EqOn (fun t : ℝ => f a + F t) f (uIcc a b) := by
    intro t ht
    have ht' : t ∈ Icc a b := by
      rw [uIcc_of_le hab] at ht
      exact ht
    have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
    have h := hfg a t ha ht' ht'.1
    simpa [F] using h.symm
  have hfAC : AbsolutelyContinuousOnInterval f a b := hbase.congr hEq
  have hFderiv : ∀ᵐ t ∂(volume.restrict (Icc a b)),
      HasDerivAt F (g t) t := by
    filter_upwards [hgInt.ae_hasDerivAt_integral.filter_mono ae_restrict_le,
      ae_restrict_mem measurableSet_Icc] with t hFt ht
    have ht' : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ht
    have ha' : a ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩
    have h := hFt ht' a ha'
    simpa [F] using h
  have hderivOpen : ∀ᵐ t ∂(volume.restrict (Ioo a b)), deriv f t = g t := by
    filter_upwards [(ae_mono (Measure.restrict_mono_set volume Ioo_subset_Icc_self)
        hFderiv),
      ae_restrict_mem measurableSet_Ioo] with t hFt ht
    have hlocal : (fun s : ℝ => f s) =ᶠ[nhds t]
        (fun s => f a + F s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      have hs' : s ∈ uIcc a b := by
        rw [uIcc_of_le hab]
        exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      exact (hEq hs').symm
    have hsum : HasDerivAt (fun s : ℝ => f a + F s) (g t) t :=
      hFt.const_add (f a)
    have hf : HasDerivAt f (g t) t := hsum.congr_of_eventuallyEq hlocal
    exact hf.deriv
  have hrestrict : (volume.restrict (Icc a b) : Measure ℝ) =
      volume.restrict (Ioo a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  refine ⟨hfAC, ?_⟩
  rw [hrestrict]
  exact hderivOpen

/-- The D3c ordered H¹ identity supplies absolute continuity and its
almost-everywhere derivative on the closed interval
(`lem:lps-H1-estimate`). -/
theorem lps_h1_energy_ac_of_ordered_identity
    {a b : ℝ} {Du : ParabolicPoint → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    (hab : a ≤ b)
    (hDtu : MemLp Dtu 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo a b))))
    (hD2u : MemLp D2u 2
      (volume.restrict (spaceTimeSet Set.univ (Ioo a b))))
    (hIdentity : ∀ s t, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) =
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, s) i j) ^ 2) -
          2 * ∫ z in spaceTimeSet Set.univ (Ioo s t),
            ∑ i, Dtu z i * (∑ j, D2u z i j j)) :
    AbsolutelyContinuousOnInterval
        (fun t : ℝ => ∫ x : Vec3,
          ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) a b ∧
      ∀ᵐ t ∂(volume.restrict (Icc a b)),
        deriv (fun t : ℝ => ∫ x : Vec3,
          ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) t =
          -2 * ∫ x : Vec3,
            ∑ i, Dtu (x, t) i * (∑ j, D2u (x, t) i j j) := by
  obtain ⟨_hprodDensity, htimeOpen, hproduct⟩ :=
    lps_h1_chain_density_integrable hDtu hD2u
  let q : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, Dtu (parabolicHomeomorph.symm z) i *
      (∑ j : Fin 3, D2u (parabolicHomeomorph.symm z) i j j)
  let G : ℝ → ℝ := fun t => ∫ x : Vec3,
    ∑ i : Fin 3, Dtu ((x, t) : ParabolicPoint) i *
      (∑ j : Fin 3, D2u ((x, t) : ParabolicPoint) i j j)
  have htimeOpen' : IntegrableOn (fun t : ℝ => -2 * G t)
      (Ioo a b) volume := by
    apply (htimeOpen.const_mul (-2)).congr
    filter_upwards [] with t
    rfl
  have hrestrict : (volume.restrict (Icc a b) : Measure ℝ) =
      volume.restrict (Ioo a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  have htime : IntegrableOn
      (fun t : ℝ => -2 * G t) (Icc a b) volume := by
    rw [IntegrableOn, hrestrict]
    exact htimeOpen'
  have hfg : ∀ s t, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) =
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, s) i j) ^ 2) +
          ∫ r in s..t, -2 * G r := by
    intro s t hs ht hst
    have hset := lps_h1_chain_setIntegral_eq_intervalIntegral
      (a := a) (b := b) (s := s) (t := t) hproduct hs ht hst
    have hGpoint : ∀ r : ℝ, (∫ x : Vec3, q (x, r)) = G r := by
      intro r
      apply integral_congr_ae
      filter_upwards [] with x
      rfl
    have hqidentity :
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) =
          (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, s) i j) ^ 2) -
            2 * ∫ z in spaceTimeSet Set.univ (Ioo s t),
              q (parabolicHomeomorph z) := by
      convert hIdentity s t hs ht hst using 1
      congr 1
    rw [hset] at hqidentity
    rw [← intervalIntegral.integral_const_mul] at hqidentity
    have hscale :
        -(∫ r in s..t, 2 * ∫ x : Vec3, q (x, r)) =
          ∫ r in s..t, -2 * ∫ x : Vec3, q (x, r) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      ring
    have hqidentity' :
        (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, t) i j) ^ 2) =
          (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, (Du (x, s) i j) ^ 2) +
            ∫ r in s..t, -2 * G r := by
      calc
        _ = (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
              (Du (x, s) i j) ^ 2) -
              ∫ r in s..t, 2 * ∫ x : Vec3, q (x, r) := hqidentity
        _ = (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
              (Du (x, s) i j) ^ 2) +
              ∫ r in s..t, -2 * ∫ x : Vec3, q (x, r) := by
          rw [sub_eq_add_neg]
          congr 1
        _ = (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
              (Du (x, s) i j) ^ 2) + ∫ r in s..t, -2 * G r := by
          congr 1
    exact hqidentity'
  simpa [G] using lps_ac_of_ordered_interval_integral hab htime hfg

end ESS.LPS

end
