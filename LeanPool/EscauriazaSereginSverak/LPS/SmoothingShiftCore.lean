/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongShift
public import LeanPool.CaffarelliKohnNirenberg.Setting.PressureGaugeSlices
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand

/-!
# Time translation between slabs

For `h : ℝ` the translation `(x, t) ↦ (x, t + h)` maps the slab over `(c, d)`
onto the slab over `(c + h, d + h)` and preserves Lebesgue measure. A
space-time weak derivative identity on a slab over `(a, b)` therefore passes to
the translated fields on every slab over `(c, d)` with `a ≤ c + h` and
`d + h ≤ b`. These are the time-translation steps of the difference-quotient
argument in `prop:lps-smoothing`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic
noncomputable section
namespace ESS.LPS

/-- The forward time translation `(x, t) ↦ (x, t + h)` preserves Lebesgue measure. -/
theorem lps_forwardShift_measurePreserving (h : ℝ) :
    MeasurePreserving (fun z : ParabolicPoint => ((z.1, z.2 + h) : ParabolicPoint))
      (volume : Measure ParabolicPoint) volume := by
  have hmp := (MeasurePreserving.id (volume : Measure Vec3)).prod
    (measurePreserving_add_right (volume : Measure ℝ) h)
  rw [← Measure.volume_eq_prod] at hmp
  exact hmp

/-- The forward time translation is a measurable embedding. -/
theorem lps_forwardShift_measurableEmbedding (h : ℝ) :
    MeasurableEmbedding (fun z : ParabolicPoint => ((z.1, z.2 + h) : ParabolicPoint)) :=
  MeasurableEmbedding.id.prodMap (measurableEmbedding_addRight h)

/-- The preimage of a translated slab under the forward time translation. -/
theorem lps_forwardShift_preimage_slab (c d h : ℝ) :
    (fun z : ParabolicPoint => ((z.1, z.2 + h) : ParabolicPoint)) ⁻¹'
        spaceTimeSet (Set.univ : Set Vec3) (Ioo (c + h) (d + h)) =
      spaceTimeSet (Set.univ : Set Vec3) (Ioo c d) := by
  ext z
  change (z.1 ∈ Set.univ ∧ z.2 + h ∈ Ioo (c + h) (d + h)) ↔ (z.1 ∈ Set.univ ∧ z.2 ∈ Ioo c d)
  simp only [Set.mem_univ, true_and, Set.mem_Ioo]
  constructor
  · intro hz
    exact ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
  · intro hz
    exact ⟨by linarith only [hz.1], by linarith only [hz.2]⟩

/-- A slab over a subinterval is contained in the slab over the interval. -/
theorem lps_slab_subset {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) :
    spaceTimeSet (Set.univ : Set Vec3) (Ioo c d) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo a b) :=
  Set.prod_mono subset_rfl (Ioo_subset_Ioo hac hdb)

/-- The slab over an open interval is measurable. -/
theorem lps_measurableSet_slab (a b : ℝ) :
    MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) :=
  MeasurableSet.univ.prod measurableSet_Ioo

/-- Change of variables for the forward time translation between slabs. -/
theorem lps_setIntegral_forwardShift (c d h : ℝ) (g : ParabolicPoint → ℝ) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo c d), g ((z.1, z.2 + h) : ParabolicPoint)) =
      ∫ w in spaceTimeSet (Set.univ : Set Vec3) (Ioo (c + h) (d + h)), g w := by
  rw [← lps_forwardShift_preimage_slab c d h]
  exact (lps_forwardShift_measurePreserving h).setIntegral_preimage_emb
    (lps_forwardShift_measurableEmbedding h) g _

/-- Integrability of a field on a slab passes to the translated field on every slab
whose translate lies inside. -/
theorem lps_memLp_forwardShift {E : Type} [NormedAddCommGroup E] {p : ENNReal}
    {a b c d h : ℝ} (hac : a ≤ c + h) (hdb : d + h ≤ b) {f : ParabolicPoint → E}
    (hf : MemLp f p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)))) :
    MemLp (fun z : ParabolicPoint => f ((z.1, z.2 + h) : ParabolicPoint)) p
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))) := by
  have hsub : MemLp f p
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo (c + h) (d + h)))) :=
    hf.mono_measure (Measure.restrict_mono (lps_slab_subset hac hdb) le_rfl)
  rw [← lps_forwardShift_preimage_slab c d h]
  exact hsub.comp_measurePreserving
    ((lps_forwardShift_measurePreserving h).restrict_preimage_emb
      (lps_forwardShift_measurableEmbedding h) _)

/-- Integrability on a slab passes to every slab over a subinterval. -/
theorem lps_memLp_slab_mono {E : Type} [NormedAddCommGroup E] {p : ENNReal}
    {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) {f : ParabolicPoint → E}
    (hf : MemLp f p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)))) :
    MemLp f p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))) :=
  hf.mono_measure (Measure.restrict_mono (lps_slab_subset hac hdb) le_rfl)

/-- An almost-everywhere property on a slab passes to the translated points of every
slab whose translate lies inside. -/
theorem lps_ae_forwardShift {a b c d h : ℝ} (hac : a ≤ c + h) (hdb : d + h ≤ b)
    {P : ParabolicPoint → Prop}
    (hP : ∀ᵐ w ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))), P w) :
    ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))),
      P ((z.1, z.2 + h) : ParabolicPoint) := by
  have hsub : ∀ᵐ w ∂(volume.restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo (c + h) (d + h)))), P w :=
    ae_restrict_of_ae_restrict_of_subset (lps_slab_subset hac hdb) hP
  rw [← lps_forwardShift_preimage_slab c d h]
  exact ((lps_forwardShift_measurePreserving h).restrict_preimage_emb
    (lps_forwardShift_measurableEmbedding h) _).quasiMeasurePreserving.ae hsub

/-- An almost-everywhere property on a slab holds on every slab over a subinterval. -/
theorem lps_ae_slab_mono {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b)
    {P : ParabolicPoint → Prop}
    (hP : ∀ᵐ w ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))), P w) :
    ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))), P z :=
  ae_restrict_of_ae_restrict_of_subset (lps_slab_subset hac hdb) hP

/-- A test function on the slab over `(c, d)`, translated backward by `h`, is a test
function on the slab over `(c + h, d + h)`. -/
theorem lps_testFunction_backShift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {c d : ℝ} (h : ℝ) {φ : Vec3 × ℝ → V}
    (hφ : φ ∈ spaceTimeTestFunction (V := V) (Set.univ : Set Vec3) (Ioo c d)) :
    (fun w : ParabolicPoint => φ ((w.1, w.2 - h) : ParabolicPoint)) ∈
      spaceTimeTestFunction (V := V) (Set.univ : Set Vec3) (Ioo (c + h) (d + h)) := by
  obtain ⟨hsm, hcpt, hts⟩ := hφ
  let e : Vec3 × ℝ ≃ₜ Vec3 × ℝ :=
    Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.subRight h)
  have hfun : (fun w : ParabolicPoint => φ ((w.1, w.2 - h) : ParabolicPoint)) = φ ∘ e := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact hsm.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))
  · rw [hfun]
    exact hcpt.comp_homeomorph e
  · rw [hfun, tsupport_comp_eq_preimage]
    intro w hw
    have h2 := (hts hw).2
    have he : (e w).2 = w.2 - h := rfl
    rw [he] at h2
    exact ⟨Set.mem_univ _, by linarith only [h2.1], by linarith only [h2.2]⟩

/-- A test function on a slab is a test function on every larger slab. -/
theorem lps_testFunction_slab_mono {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) {φ : Vec3 × ℝ → V}
    (hφ : φ ∈ spaceTimeTestFunction (V := V) (Set.univ : Set Vec3) (Ioo c d)) :
    φ ∈ spaceTimeTestFunction (V := V) (Set.univ : Set Vec3) (Ioo a b) :=
  ⟨hφ.1, hφ.2.1, hφ.2.2.trans (lps_slab_subset hac hdb)⟩

/-- The integral over a slab of a function vanishing outside a smaller slab is its
integral over the smaller slab. -/
theorem lps_setIntegral_slab_eq_of_vanish {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b)
    {K : ParabolicPoint → ℝ}
    (hK : ∀ z : ParabolicPoint, z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo c d) → K z = 0) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), K z) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo c d), K z :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (lps_measurableSet_slab a b)
    (lps_slab_subset hac hdb) fun z hz => hK z hz.2

/-- Values and first derivatives of a scalar test vanish outside its slab. -/
theorem lps_test_vanish {c d : ℝ} {φ : ParabolicPoint → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo c d))
    {z : ParabolicPoint} (hz : z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo c d)) :
    φ z = 0 ∧ (∀ j : Fin 3, spatialPartial φ j z = 0) ∧ timePartial φ z = 0 := by
  let ψ : Vec3 × ℝ → ℝ := φ
  let y : Vec3 × ℝ := z
  have hns : y ∉ tsupport ψ := fun hmem => hz (hφ.2.2 hmem)
  have h0 : ψ y = 0 := image_eq_zero_of_notMem_tsupport hns
  exact ⟨h0,
    fun j => spatialPartial_eq_zero_off_tsupport hns j,
    timePartial_eq_zero_off_tsupport hns⟩

/-- Spatial derivatives of a backward-translated test, at a forward-translated point. -/
theorem lps_backShift_spatialPartial (h : ℝ) (φ : ParabolicPoint → ℝ) (j : Fin 3)
    (z : ParabolicPoint) :
    spatialPartial (fun w : ParabolicPoint => φ ((w.1, w.2 - h) : ParabolicPoint)) j
        ((z.1, z.2 + h) : ParabolicPoint) = spatialPartial φ j z := by
  unfold spatialPartial
  simp only [add_sub_cancel_right]

/-- Time derivative of a backward-translated test, at a forward-translated point. -/
theorem lps_backShift_timePartial (h : ℝ) (φ : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    timePartial (fun w : ParabolicPoint => φ ((w.1, w.2 - h) : ParabolicPoint))
        ((z.1, z.2 + h) : ParabolicPoint) = timePartial φ z := by
  unfold timePartial
  have hd := fderiv_comp_sub (𝕜 := ℝ) (f := fun s : ℝ => φ (z.1, s)) (x := z.2 + h) h
  simp only at hd ⊢
  rw [hd, add_sub_cancel_right]

/-- Value of a backward-translated test at a forward-translated point. -/
theorem lps_backShift_value {V : Type} (h : ℝ) (φ : ParabolicPoint → V) (z : ParabolicPoint) :
    (fun w : ParabolicPoint => φ ((w.1, w.2 - h) : ParabolicPoint))
      ((z.1, z.2 + h) : ParabolicPoint) = φ z := by
  simp only [add_sub_cancel_right]
  rfl

/-- The integral over a slab of a function vanishing outside a translated subslab,
written as an integral over the untranslated subslab. -/
theorem lps_setIntegral_slab_forwardShift {a b c d h : ℝ} (hac : a ≤ c + h) (hdb : d + h ≤ b)
    (K : ParabolicPoint → ℝ)
    (hK : ∀ z : ParabolicPoint,
      z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo (c + h) (d + h)) → K z = 0) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), K z) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo c d), K ((z.1, z.2 + h) : ParabolicPoint) := by
  rw [lps_setIntegral_slab_eq_of_vanish hac hdb hK]
  exact (lps_setIntegral_forwardShift c d h K).symm

/-- Space-time weak derivatives on a slab pass to the time-translated fields on every
slab whose translate lies inside (`prop:lps-smoothing`). -/
theorem lps_hasSpaceTimeWeakDerivs_forwardShift {a b c d h : ℝ}
    (hac : a ≤ c + h) (hdb : d + h ≤ b) {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtu : ParabolicPoint → Vec3}
    (hw : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo a b) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)))) :
    HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo c d)
      (fun z => u ((z.1, z.2 + h) : ParabolicPoint))
      (fun z => Du ((z.1, z.2 + h) : ParabolicPoint))
      (fun z => D2u ((z.1, z.2 + h) : ParabolicPoint))
      (fun z => Dtu ((z.1, z.2 + h) : ParabolicPoint)) := by
  obtain ⟨-, -, -, -, hid⟩ := hw
  refine ⟨lps_locallyIntegrableOn_of_memLp (lps_memLp_forwardShift hac hdb hu),
    lps_locallyIntegrableOn_of_memLp (lps_memLp_forwardShift hac hdb hDu),
    lps_locallyIntegrableOn_of_memLp (lps_memLp_forwardShift hac hdb hD2u),
    lps_locallyIntegrableOn_of_memLp (lps_memLp_forwardShift hac hdb hDtu), ?_⟩
  intro φ hφ
  have hφs := lps_testFunction_backShift (V := ℝ) h hφ
  have hφb := lps_testFunction_slab_mono (V := ℝ) hac hdb hφs
  obtain ⟨h1, h2, h3⟩ := hid _ hφb
  have htr := lps_setIntegral_slab_forwardShift hac hdb
  have hv := fun (z : ParabolicPoint) hz => lps_test_vanish hφs (z := z) hz
  refine ⟨fun i j => ?_, fun i j k => ?_, fun i => ?_⟩
  · have e := h1 i j
    rw [htr (fun z => u z i * spatialPartial (fun w : ParabolicPoint => φ ((w.1, w.2 - h) : ParabolicPoint)) j z)
        (fun z hz => mul_eq_zero_of_right _ ((hv z hz).2.1 j)),
      htr (fun z => Du z i j * φ ((z.1, z.2 - h) : ParabolicPoint))
        (fun z hz => mul_eq_zero_of_right _ (hv z hz).1)] at e
    simpa only [lps_backShift_spatialPartial, lps_backShift_value] using e
  · have e := h2 i j k
    rw [htr (fun z => Du z i j * spatialPartial (fun w : ParabolicPoint => φ ((w.1, w.2 - h) : ParabolicPoint)) k z)
        (fun z hz => mul_eq_zero_of_right _ ((hv z hz).2.1 k)),
      htr (fun z => D2u z i j k * φ ((z.1, z.2 - h) : ParabolicPoint))
        (fun z hz => mul_eq_zero_of_right _ (hv z hz).1)] at e
    simpa only [lps_backShift_spatialPartial, lps_backShift_value] using e
  · have e := h3 i
    rw [htr (fun z => u z i * timePartial (fun w : ParabolicPoint => φ ((w.1, w.2 - h) : ParabolicPoint)) z)
        (fun z hz => mul_eq_zero_of_right _ (hv z hz).2.2),
      htr (fun z => Dtu z i * φ ((z.1, z.2 - h) : ParabolicPoint))
        (fun z hz => mul_eq_zero_of_right _ (hv z hz).1)] at e
    simpa only [lps_backShift_timePartial, lps_backShift_value] using e

/-- The weak momentum equation with a time-derivative field, on a slab, passes to the
time-translated fields on every slab whose translate lies inside (`prop:lps-smoothing`). -/
theorem lps_weakEquation_forwardShift {a b c d h : ℝ} (hac : a ≤ c + h) (hdb : d + h ≤ b)
    {A : ParabolicPoint → Vec3} {F : ParabolicPoint → Fin 3 → Fin 3 → ℝ}
    {G : ParabolicPoint → Fin 3 → Vec3} {q : ParabolicPoint → ℝ}
    (heq : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a b) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b),
        (∑ i, A z i * φ z i - ∑ i, ∑ j, F z i j * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, G z i j * spatialPartial (fun y => φ y i) j z
          - q z * ∑ i, spatialPartial (fun y => φ y i) i z) = 0) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo c d) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo c d),
        (∑ i, A ((z.1, z.2 + h) : ParabolicPoint) i * φ z i
          - ∑ i, ∑ j, F ((z.1, z.2 + h) : ParabolicPoint) i j * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, G ((z.1, z.2 + h) : ParabolicPoint) i j * spatialPartial (fun y => φ y i) j z
          - q ((z.1, z.2 + h) : ParabolicPoint) * ∑ i, spatialPartial (fun y => φ y i) i z) = 0 := by
  intro φ hφ
  have hφs := lps_testFunction_backShift (V := Vec3) h hφ
  have hφb := lps_testFunction_slab_mono (V := Vec3) hac hdb hφs
  have e := heq _ hφb
  rw [lps_setIntegral_slab_forwardShift hac hdb _ ?_] at e
  · have hV : ∀ (z : ParabolicPoint) (i : Fin 3),
        φ ((z.1, z.2 + h - h) : ParabolicPoint) i = φ z i := by
      intro z i
      rw [add_sub_cancel_right]
      rfl
    have hS : ∀ (z : ParabolicPoint) (i j : Fin 3),
        spatialPartial (fun y : ParabolicPoint => φ ((y.1, y.2 - h) : ParabolicPoint) i) j
          ((z.1, z.2 + h) : ParabolicPoint) = spatialPartial (fun y => φ y i) j z :=
      fun z i j => lps_backShift_spatialPartial h (fun y => φ y i) j z
    simpa only [hV, hS] using e
  · intro z hz
    have hv := fun i : Fin 3 =>
      lps_test_vanish (CKN.component_mem_spaceTimeTestFunction hφs i) hz
    have h1 : ∀ i : Fin 3, φ ((z.1, z.2 - h) : ParabolicPoint) i = 0 := fun i => (hv i).1
    have h2 : ∀ i j : Fin 3,
        spatialPartial (fun y : ParabolicPoint => φ ((y.1, y.2 - h) : ParabolicPoint) i) j z = 0 :=
      fun i j => (hv i).2.1 j
    simp only [h1, h2, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

/-- Space-time weak derivatives on a slab restrict to every slab over a subinterval. -/
theorem lps_hasSpaceTimeWeakDerivs_slab_mono {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hw : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo a b) u Du D2u Dtu) :
    HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo c d) u Du D2u Dtu := by
  obtain ⟨hu, hDu, hD2u, hDtu, hid⟩ := hw
  have hsub := lps_slab_subset hac hdb
  refine ⟨hu.mono_set hsub, hDu.mono_set hsub, hD2u.mono_set hsub, hDtu.mono_set hsub, ?_⟩
  intro φ hφ
  obtain ⟨h1, h2, h3⟩ := hid φ (lps_testFunction_slab_mono (V := ℝ) hac hdb hφ)
  have hv := fun (z : ParabolicPoint) hz => lps_test_vanish hφ (z := z) hz
  have hr := fun K hK => lps_setIntegral_slab_eq_of_vanish (a := a) (b := b) hac hdb (K := K) hK
  refine ⟨fun i j => ?_, fun i j k => ?_, fun i => ?_⟩
  · rw [← hr (fun z => u z i * spatialPartial φ j z)
        (fun z hz => mul_eq_zero_of_right _ ((hv z hz).2.1 j)),
      ← hr (fun z => Du z i j * φ z) (fun z hz => mul_eq_zero_of_right _ (hv z hz).1)]
    exact h1 i j
  · rw [← hr (fun z => Du z i j * spatialPartial φ k z)
        (fun z hz => mul_eq_zero_of_right _ ((hv z hz).2.1 k)),
      ← hr (fun z => D2u z i j k * φ z) (fun z hz => mul_eq_zero_of_right _ (hv z hz).1)]
    exact h2 i j k
  · rw [← hr (fun z => u z i * timePartial φ z)
        (fun z hz => mul_eq_zero_of_right _ (hv z hz).2.2),
      ← hr (fun z => Dtu z i * φ z) (fun z hz => mul_eq_zero_of_right _ (hv z hz).1)]
    exact h3 i

/-- The weak momentum equation with a time-derivative field, on a slab, restricts to every
slab over a subinterval. -/
theorem lps_weakEquation_slab_mono {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b)
    {A : ParabolicPoint → Vec3} {F : ParabolicPoint → Fin 3 → Fin 3 → ℝ}
    {G : ParabolicPoint → Fin 3 → Vec3} {q : ParabolicPoint → ℝ}
    (heq : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo a b) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b),
        (∑ i, A z i * φ z i - ∑ i, ∑ j, F z i j * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, G z i j * spatialPartial (fun y => φ y i) j z
          - q z * ∑ i, spatialPartial (fun y => φ y i) i z) = 0) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo c d) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo c d),
        (∑ i, A z i * φ z i - ∑ i, ∑ j, F z i j * spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, G z i j * spatialPartial (fun y => φ y i) j z
          - q z * ∑ i, spatialPartial (fun y => φ y i) i z) = 0 := by
  intro φ hφ
  rw [← lps_setIntegral_slab_eq_of_vanish hac hdb ?_]
  · exact heq φ (lps_testFunction_slab_mono (V := Vec3) hac hdb hφ)
  · intro z hz
    have hv := fun i : Fin 3 =>
      lps_test_vanish (CKN.component_mem_spaceTimeTestFunction hφ i) hz
    have h1 : ∀ i : Fin 3, φ z i = 0 := fun i => (hv i).1
    have h2 : ∀ i j : Fin 3, spatialPartial (fun y => φ y i) j z = 0 :=
      fun i j => (hv i).2.1 j
    simp only [h1, h2, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

end ESS.LPS
