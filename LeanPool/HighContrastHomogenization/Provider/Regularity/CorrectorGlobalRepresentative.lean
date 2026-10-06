/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalH1

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorGlobalRepresentative

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Global representatives of projective local correctors

Compatible local value and gradient `L²` classes are glued along the disjoint
shells of the centered-cube exhaustion.  The resulting raw fields are strongly
measurable and agree almost everywhere with every stored local component.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

/-- The disjoint shell added at the `n`th stage of the centered-cube
exhaustion. -/
@[expose]
def localGradientShell (d : ℕ) : ℕ → Set (Vec d)
  | 0 => localGradientCube d 0
  | n + 1 => localGradientCube d (n + 1) \ localGradientCube d n

/-- Every exhaustion shell is measurable. -/
theorem measurableSet_localGradientShell (d n : ℕ) :
    MeasurableSet (localGradientShell d n) := by
  cases n with
  | zero =>
      exact measurableSet_openCubeSet (originCube d (0 : ℤ))
  | succ n =>
      exact (measurableSet_openCubeSet (originCube d ((n + 1 : ℕ) : ℤ))).diff
        (measurableSet_openCubeSet (originCube d (n : ℤ)))

/-- The `n`th shell lies in the `n`th exhaustion cube. -/
theorem localGradientShell_subset_cube (d n : ℕ) :
    localGradientShell d n ⊆ localGradientCube d n := by
  cases n with
  | zero => exact fun _ hx => hx
  | succ n => exact Set.sdiff_subset

/-- Adding the successor shell to an exhaustion cube gives the next cube. -/
theorem localGradientCube_union_shell (d n : ℕ) :
    localGradientCube d n ∪ localGradientShell d (n + 1) =
      localGradientCube d (n + 1) := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact localGradientCube_mono (Nat.le_succ n) hx
    · exact hx.1
  · intro hx
    by_cases hxn : x ∈ localGradientCube d n
    · exact Or.inl hxn
    · exact Or.inr ⟨hx, hxn⟩

/-- Distinct exhaustion shells are disjoint. -/
theorem pairwise_disjoint_localGradientShell (d : ℕ) :
    Pairwise fun i j => Disjoint (localGradientShell d i) (localGradientShell d j) := by
  have hforward : ∀ {i j : ℕ}, i < j →
      Disjoint (localGradientShell d i) (localGradientShell d j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    cases j with
    | zero => omega
    | succ j =>
        have hij' : i ≤ j := by omega
        have hxicube : x ∈ localGradientCube d i :=
          localGradientShell_subset_cube d i hxi
        have hxjcube : x ∈ localGradientCube d j :=
          localGradientCube_mono hij' hxicube
        exact hxj.2 hxjcube
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact hforward hijlt
  · exact (hforward hjilt).symm

/-- The shells exhaust the whole Euclidean space. -/
theorem iUnion_localGradientShell (d : ℕ) :
    ⋃ n, localGradientShell d n = Set.univ := by
  have hcube : ∀ n : ℕ,
      localGradientCube d n ⊆ ⋃ k, localGradientShell d k := by
    intro n
    induction n with
    | zero =>
        intro x hx
        exact Set.mem_iUnion.mpr ⟨0, hx⟩
    | succ n ih =>
        intro x hx
        rw [← localGradientCube_union_shell d n] at hx
        rcases hx with hx | hx
        · exact ih hx
        · exact Set.mem_iUnion.mpr ⟨n + 1, hx⟩
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ n, localGradientCube d n := by
    rw [iUnion_localGradientCube]
    trivial
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  exact hcube n hxn

theorem localGradientShell_compat
    {d : ℕ} {E : Type*}
    (f : ∀ n, localGradientShell d n → E)
    (i j : ℕ) (x : Vec d)
    (hxi : x ∈ localGradientShell d i)
    (hxj : x ∈ localGradientShell d j) :
    f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ := by
  by_cases hij : i = j
  · subst j
    rfl
  · exact False.elim
      (Set.disjoint_left.mp (pairwise_disjoint_localGradientShell d hij)
        hxi hxj)

/-- Glue arbitrary shellwise fields into a global field. -/
@[expose]
noncomputable def localGradientShellLift {d : ℕ} {E : Type*}
    (f : ∀ n, localGradientShell d n → E) : Vec d → E :=
  Set.liftCover (localGradientShell d) f (localGradientShell_compat f)
    (iUnion_localGradientShell d)

/-- The shell lift reads the supplied field on each shell. -/
theorem localGradientShellLift_of_mem {d : ℕ} {E : Type*}
    (f : ∀ n, localGradientShell d n → E) (n : ℕ) {x : Vec d}
    (hx : x ∈ localGradientShell d n) :
    localGradientShellLift f x = f n ⟨x, hx⟩ := by
  exact Set.liftCover_of_mem hx

/-- Measurable shellwise fields have a measurable shell lift. -/
theorem measurable_localGradientShellLift {d : ℕ} {E : Type*}
    [MeasurableSpace E]
    (f : ∀ n, localGradientShell d n → E)
    (hf : ∀ n, Measurable (f n)) :
    Measurable (localGradientShellLift f) := by
  exact measurable_liftCover (localGradientShell d)
    (measurableSet_localGradientShell d) f hf
      (localGradientShell_compat f) (iUnion_localGradientShell d)

@[expose]
public noncomputable def localValueStrongRepresentative {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) : Vec d → ℝ :=
  let h := (Lp.memLp (z.valueComponent n)).aestronglyMeasurable
  h.mk (z.valueComponent n)

private theorem stronglyMeasurable_localValueStrongRepresentative {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    StronglyMeasurable (localValueStrongRepresentative z n) := by
  exact (Lp.memLp (z.valueComponent n)).aestronglyMeasurable.stronglyMeasurable_mk

private theorem valueComponent_ae_eq_localValueStrongRepresentative {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    z.valueComponent n
      =ᵐ[volumeMeasureOn (localGradientCube d n)]
        localValueStrongRepresentative z n := by
  exact (Lp.memLp (z.valueComponent n)).aestronglyMeasurable.ae_eq_mk

private theorem localValueStrongRepresentative_ae_eq_of_le {d m n : ℕ}
    (z : NormalizedLocalH1Carrier d) (hmn : m ≤ n) :
    localValueStrongRepresentative z m
      =ᵐ[volumeMeasureOn (localGradientCube d m)]
        localValueStrongRepresentative z n := by
  have hcomponent :
      z.valueComponent m
        =ᵐ[volumeMeasureOn (localGradientCube d m)] z.valueComponent n := by
    have h := localValueRestrict_coeFn_ae hmn (z.valueComponent n)
    have heq : localValueRestrict hmn (z.valueComponent n) =
        z.valueComponent m := by
      exact LocalValueCarrier.restrict_component z.value hmn
    rw [heq] at h
    exact h
  exact
    (valueComponent_ae_eq_localValueStrongRepresentative z m).symm.trans
      (hcomponent.trans
        ((valueComponent_ae_eq_localValueStrongRepresentative z n).filter_mono
          (ae_mono (Measure.restrict_mono_set volume
            (localGradientCube_mono hmn)))))

@[expose]
public noncomputable def localGradientVectorComponent {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    VectorL2 (localGradientCube d n) :=
  hilbertVectorL2ToVectorL2 (z.gradientComponent n)

@[expose]
public noncomputable def localGradientStrongRepresentative {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) : Vec d → Vec d :=
  let h := (Lp.memLp (localGradientVectorComponent z n)).aestronglyMeasurable
  h.mk (localGradientVectorComponent z n)

private theorem stronglyMeasurable_localGradientStrongRepresentative {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    StronglyMeasurable (localGradientStrongRepresentative z n) := by
  exact (Lp.memLp (localGradientVectorComponent z n)).aestronglyMeasurable.stronglyMeasurable_mk

private theorem localGradientVectorComponent_ae_eq_strongRepresentative {d : ℕ}
    (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    localGradientVectorComponent z n
      =ᵐ[volumeMeasureOn (localGradientCube d n)]
        localGradientStrongRepresentative z n := by
  exact (Lp.memLp (localGradientVectorComponent z n)).aestronglyMeasurable.ae_eq_mk

private theorem localGradientVectorComponent_ae_eq_of_le {d m n : ℕ}
    (z : NormalizedLocalH1Carrier d) (hmn : m ≤ n) :
    localGradientVectorComponent z m
      =ᵐ[volumeMeasureOn (localGradientCube d m)]
        localGradientVectorComponent z n := by
  have hcomponent :
      z.gradientComponent m
        =ᵐ[volumeMeasureOn (localGradientCube d m)] z.gradientComponent n := by
    have h := localGradientRestrict_coeFn_ae hmn (z.gradientComponent n)
    have heq : localGradientRestrict hmn (z.gradientComponent n) =
        z.gradientComponent m := by
      exact LocalGradientCarrier.restrict_component z.gradient hmn
    rw [heq] at h
    exact h
  simpa only [localGradientVectorComponent] using
    (coeFn_hilbertVectorL2ToVectorL2
      (U := localGradientCube d m) (f := z.gradientComponent m)).trans
      ((hcomponent.fun_comp fun y => y.toVec).trans
        ((coeFn_hilbertVectorL2ToVectorL2
          (U := localGradientCube d n) (f := z.gradientComponent n)).filter_mono
          (ae_mono (Measure.restrict_mono_set volume
            (localGradientCube_mono hmn)))).symm)

private theorem localGradientStrongRepresentative_ae_eq_of_le {d m n : ℕ}
    (z : NormalizedLocalH1Carrier d) (hmn : m ≤ n) :
    localGradientStrongRepresentative z m
      =ᵐ[volumeMeasureOn (localGradientCube d m)]
        localGradientStrongRepresentative z n := by
  exact
    (localGradientVectorComponent_ae_eq_strongRepresentative z m).symm.trans
      ((localGradientVectorComponent_ae_eq_of_le z hmn).trans
        ((localGradientVectorComponent_ae_eq_strongRepresentative z n).filter_mono
          (ae_mono (Measure.restrict_mono_set volume
            (localGradientCube_mono hmn)))))

/-- A global scalar representative of the projective local value classes. -/
@[expose]
noncomputable def NormalizedLocalH1Carrier.globalValueRepresentative {d : ℕ}
    (z : NormalizedLocalH1Carrier d) : Vec d → ℝ :=
  localGradientShellLift fun n x => localValueStrongRepresentative z n x

/-- A global Euclidean representative of the projective local gradient
classes. -/
@[expose]
noncomputable def NormalizedLocalH1Carrier.globalGradientRepresentative {d : ℕ}
    (z : NormalizedLocalH1Carrier d) : Vec d → Vec d :=
  localGradientShellLift fun n x => localGradientStrongRepresentative z n x

/-- The global value representative is strongly measurable. -/
theorem NormalizedLocalH1Carrier.stronglyMeasurable_globalValueRepresentative
    {d : ℕ} (z : NormalizedLocalH1Carrier d) :
    StronglyMeasurable z.globalValueRepresentative := by
  exact (measurable_localGradientShellLift _ fun n =>
    (stronglyMeasurable_localValueStrongRepresentative z n).measurable.comp
      measurable_subtype_coe).stronglyMeasurable

/-- The global gradient representative is strongly measurable. -/
theorem NormalizedLocalH1Carrier.stronglyMeasurable_globalGradientRepresentative
    {d : ℕ} (z : NormalizedLocalH1Carrier d) :
    StronglyMeasurable z.globalGradientRepresentative := by
  exact (measurable_localGradientShellLift _ fun n =>
    (stronglyMeasurable_localGradientStrongRepresentative z n).measurable.comp
      measurable_subtype_coe).stronglyMeasurable

private theorem NormalizedLocalH1Carrier.globalValueRepresentative_ae_eq_strong
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    z.globalValueRepresentative
      =ᵐ[volumeMeasureOn (localGradientCube d n)]
        localValueStrongRepresentative z n := by
  induction n with
  | zero =>
      exact ae_restrict_of_forall_mem (measurableSet_localGradientShell d 0)
        fun _ hx => localGradientShellLift_of_mem _ 0 hx
  | succ n ih =>
      rw [← localGradientCube_union_shell d n]
      change ∀ᵐ x ∂volume.restrict
        (localGradientCube d n ∪ localGradientShell d (n + 1)),
          z.globalValueRepresentative x = localValueStrongRepresentative z (n + 1) x
      rw [ae_restrict_union_iff]
      constructor
      · exact ih.trans
          (localValueStrongRepresentative_ae_eq_of_le z (Nat.le_succ n))
      · exact ae_restrict_of_forall_mem
          (measurableSet_localGradientShell d (n + 1)) fun _ hx =>
            localGradientShellLift_of_mem _ (n + 1) hx

private theorem NormalizedLocalH1Carrier.globalGradientRepresentative_ae_eq_strong
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    z.globalGradientRepresentative
      =ᵐ[volumeMeasureOn (localGradientCube d n)]
        localGradientStrongRepresentative z n := by
  induction n with
  | zero =>
      exact ae_restrict_of_forall_mem (measurableSet_localGradientShell d 0)
        fun _ hx => localGradientShellLift_of_mem _ 0 hx
  | succ n ih =>
      rw [← localGradientCube_union_shell d n]
      change ∀ᵐ x ∂volume.restrict
        (localGradientCube d n ∪ localGradientShell d (n + 1)),
          z.globalGradientRepresentative x =
            localGradientStrongRepresentative z (n + 1) x
      rw [ae_restrict_union_iff]
      constructor
      · exact ih.trans
          (localGradientStrongRepresentative_ae_eq_of_le z (Nat.le_succ n))
      · exact ae_restrict_of_forall_mem
          (measurableSet_localGradientShell d (n + 1)) fun _ hx =>
            localGradientShellLift_of_mem _ (n + 1) hx

/-- On every exhaustion cube, the global scalar representative agrees almost
everywhere with the stored scalar `L²` component. -/
theorem NormalizedLocalH1Carrier.globalValueRepresentative_ae_eq_component
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    z.globalValueRepresentative
      =ᵐ[volumeMeasureOn (localGradientCube d n)] z.valueComponent n := by
  exact (z.globalValueRepresentative_ae_eq_strong n).trans
    (valueComponent_ae_eq_localValueStrongRepresentative z n).symm

/-- On every exhaustion cube, the global Euclidean gradient representative
agrees almost everywhere with the vector form of the stored gradient
component. -/
theorem NormalizedLocalH1Carrier.globalGradientRepresentative_ae_eq_component
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    z.globalGradientRepresentative
      =ᵐ[volumeMeasureOn (localGradientCube d n)]
        hilbertVectorL2ToVectorL2 (z.gradientComponent n) := by
  simpa only [localGradientVectorComponent] using
    (z.globalGradientRepresentative_ae_eq_strong n).trans
      (localGradientVectorComponent_ae_eq_strongRepresentative z n).symm

/-- The global scalar representative is square-integrable on every exhaustion
cube. -/
theorem NormalizedLocalH1Carrier.memLp_globalValueRepresentative
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    MemLp z.globalValueRepresentative 2
      (volumeMeasureOn (localGradientCube d n)) := by
  exact (memLp_congr_ae (z.globalValueRepresentative_ae_eq_component n)).mpr
    (Lp.memLp (z.valueComponent n))

/-- The global gradient representative is square-integrable on every
exhaustion cube. -/
theorem NormalizedLocalH1Carrier.memLp_globalGradientRepresentative
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    MemLp z.globalGradientRepresentative 2
      (volumeMeasureOn (localGradientCube d n)) := by
  exact (memLp_congr_ae
    (z.globalGradientRepresentative_ae_eq_component n)).mpr
      (Lp.memLp (hilbertVectorL2ToVectorL2 (z.gradientComponent n)))

/-- On each exhaustion cube, the global scalar representative agrees almost
everywhere with the canonical recovered local `H¹` function. -/
theorem NormalizedLocalH1Carrier.globalValueRepresentative_ae_eq_localH1Function
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    z.globalValueRepresentative
      =ᵐ[volumeMeasureOn (localGradientCube d n)]
        (z.localH1Function n).toFun := by
  exact (z.globalValueRepresentative_ae_eq_component n).trans
    (z.localH1Function_toFun_ae n).symm

private theorem localGradientVectorComponent_eq_localH1GradientVectorL2
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    hilbertVectorL2ToVectorL2 (z.gradientComponent n) =
      (z.localH1Function n).gradToVectorL2 := by
  rw [← z.localH1Function_gradToHilbertVectorL2 n]
  simpa [H1Function.gradToHilbertVectorL2, H1Function.gradToVectorL2] using
    hilbertVectorL2ToVectorL2_toHilbertVectorL2
      (U := localGradientCube d n) (z.localH1Function n).grad_memVectorL2

/-- On each exhaustion cube, the global Euclidean gradient representative
agrees almost everywhere with the weak gradient of the canonical recovered
local `H¹` function. -/
theorem NormalizedLocalH1Carrier.globalGradientRepresentative_ae_eq_localH1Gradient
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    z.globalGradientRepresentative
      =ᵐ[volumeMeasureOn (localGradientCube d n)]
        (z.localH1Function n).grad := by
  have h := z.globalGradientRepresentative_ae_eq_component n
  rw [localGradientVectorComponent_eq_localH1GradientVectorL2] at h
  exact h.trans (z.localH1Function n).coeFn_gradToVectorL2

end

end HighContrast
end HCPolySupport
