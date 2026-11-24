/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.PlurifineCompactness

/-! Actual local fine topology on genuine varying-dimensional complex charts. -/

@[expose] public section

namespace SGPT.PSH.VariableComplexAtlas

open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The actual open target of any actual candidate coordinate map. -/
def coordinateDomain {d : ℕ} (c : OpenPartialHomeomorph X (ComplexModel d)) :
    Opens (ComplexModel d) := ⟨c.target, c.open_target⟩

/-- The actual inverse on an arbitrary actual coordinate target. -/
noncomputable def coordinateInverse {d : ℕ} (c : OpenPartialHomeomorph X (ComplexModel d)) :
    coordinateDomain c → X := fun z ↦ c.symm z.val

/-- The actual open target of an original holomorphic chart. -/
def chartDomain (A : VariableComplexAtlas X) (i : A.Index) : Opens (ComplexModel (A.dimension i))
    :=
  ⟨(A.chart i).target, (A.chart i).open_target⟩

/-- The actual inverse chart on its actual original target. -/
noncomputable def chartInverse (A : VariableComplexAtlas X) (i : A.Index) : A.chartDomain i → X :=
  fun z ↦ (A.chart i).symm z.val

/-- The actual final topology from all original fine coordinate domains. -/
@[instance_reducible]
noncomputable def plurifineTopology (A : VariableComplexAtlas X) : TopologicalSpace X :=
  ⨆ i : A.Index, coinduced (A.chartInverse i) (domainPlurifineTopology (A.chartDomain i))

/-- Exact independent open-set characterization by original fine coordinates. -/
theorem isOpen_plurifine_iff (A : VariableComplexAtlas X) (S : Set X) :
    IsOpen[A.plurifineTopology] S ↔
      ∀ i, IsOpen[domainPlurifineTopology (A.chartDomain i)] ((A.chartInverse i) ⁻¹' S) := by
  simp only [isOpen_iSup_iff, isOpen_coinduced]

/-- Genuine ordinary inverse-chart continuity on the actual target. -/
theorem continuous_chartInverse (A : VariableComplexAtlas X) (i : A.Index) :
    Continuous (A.chartInverse i) := by
  exact continuousOn_iff_continuous_domRestrict.mp (A.chart i).symm.continuousOn

/-- The independent manifold fine topology refines its ordinary topology. -/
theorem plurifine_le_euclidean (A : VariableComplexAtlas X) :
    A.plurifineTopology ≤ (inferInstance : TopologicalSpace X) := by
  intro S hS
  apply (A.isOpen_plurifine_iff S).mpr
  intro i
  exact (hS.preimage (A.continuous_chartInverse i)).mono
    (domainPlurifine_le_euclidean (A.chartDomain i))

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.PSH
open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- The genuine fine topology compatibility makes actual ordinary-open
inclusion an actual fine-open map. -/
theorem isOpen_domainPlurifine_image_inclusion {n : ℕ}
    {Ω₁ Ω₂ : Opens (ComplexModel n)} (h₁₂ : (Ω₁ : Set (ComplexModel n)) ⊆ Ω₂)
    {S : Set Ω₁} (hS : IsOpen[domainPlurifineTopology Ω₁] S) :
    IsOpen[domainPlurifineTopology Ω₂] ((holomorphicDomainMap (F := id) h₁₂) '' S) := by
  let ι := holomorphicDomainMap (F := id) h₁₂
  rw [domainPlurifine_induced_eq h₁₂] at hS
  let : TopologicalSpace Ω₂ := domainPlurifineTopology Ω₂
  obtain ⟨W, hW, hSW⟩ := isOpen_induced_iff.mp hS
  have hr : range ι = {z : Ω₂ | z.val ∈ (Ω₁ : Set (ComplexModel n))} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hz
      exact ⟨⟨z.val, hz⟩, Subtype.ext rfl⟩
  have hR : IsOpen (range ι) := by
    rw [hr]
    exact SGPT.Foundations.Analysis.Pending.PlurifineEuclideanComparison.isOpen_euclidean Ω₁.isOpen
  have heq : ι '' S = range ι ∩ W := by
    rw [← hSW]
    exact image_preimage_eq_range_inter
  rw [heq]
  exact hR.inter hW

/-- Actual local holomorphic pullback is fine-open in the original containing
domain. The local-domain inclusion is the proved fine-open map. -/
theorem isOpen_domainPlurifine_local_holomorphic_preimage {k n : ℕ}
    {Ω : Opens (ComplexModel k)} {Ω' : Opens (ComplexModel n)}
    {D : Opens (ComplexModel k)} (hDΩ : (D : Set (ComplexModel k)) ⊆ Ω)
    {F : ComplexModel k → ComplexModel n} (hF : DifferentiableOn ℂ F D)
    (hFD : MapsTo F D Ω') {S : Set Ω'} (hS : IsOpen[domainPlurifineTopology Ω'] S) :
    IsOpen[domainPlurifineTopology Ω]
      {z : Ω | ∃ hz : z.val ∈ (D : Set (ComplexModel k)),
        holomorphicDomainMap hFD ⟨z.val, hz⟩ ∈ S} := by
  have hT := isOpen_domainPlurifine_preimage_holomorphic hF hFD hS
  have hI := isOpen_domainPlurifine_image_inclusion hDΩ hT
  convert hI using 1
  ext z
  constructor
  · rintro ⟨hz, hy⟩
    exact ⟨⟨z.val, hz⟩, hy, Subtype.ext rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩

end SGPT.PSH

namespace SGPT.PSH.VariableComplexAtlas
open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X]

/-- Actual compatibility derivatives suffice for every genuine coordinate
fine-image to be open, without supplying a fine-continuity certificate. -/
theorem isOpen_plurifine_coordinateInverse_image (A : VariableComplexAtlas X)
    {d : ℕ} (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : ∀ j, DifferentiableOn ℂ ((A.chart j).symm.trans c)
      ((A.chart j).symm.trans c).source)
    {V : Set (coordinateDomain c)}
    (hV : IsOpen[domainPlurifineTopology (coordinateDomain c)] V) :
    IsOpen[A.plurifineTopology] ((coordinateInverse c) '' V) := by
  apply (A.isOpen_plurifine_iff _).mpr
  intro j
  let e := (A.chart j).symm.trans c
  let D : Opens (ComplexModel (A.dimension j)) := ⟨e.source, e.open_source⟩
  have hDΩ : (D : Set (ComplexModel (A.dimension j))) ⊆ A.chartDomain j := by
    intro z hz
    change z ∈ (A.chart j).target
    change z ∈ ((A.chart j).symm.trans c).source at hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact hz.1
  have hFD : MapsTo e D (coordinateDomain c) := by
    intro z hz
    have ht := e.mapsTo hz
    change e z ∈ c.target
    change ((A.chart j).symm.trans c) z ∈
      ((A.chart j).symm.trans c).target at ht
    rw [OpenPartialHomeomorph.trans_target] at ht
    exact ht.1
  have h := isOpen_domainPlurifine_local_holomorphic_preimage hDΩ (hc j) hFD hV
  convert h using 1
  ext z
  constructor
  · rintro ⟨y, hy, heq⟩
    change c.symm y.val = (A.chart j).symm z.val at heq
    have hzD : z.val ∈ (D : Set (ComplexModel (A.dimension j))) := by
      change z.val ∈ ((A.chart j).symm.trans c).source
      rw [OpenPartialHomeomorph.trans_source]
      exact ⟨z.property, by
        change (A.chart j).symm z.val ∈ c.source
        rw [← heq]
        exact c.map_target y.property⟩
    have hFy : holomorphicDomainMap hFD ⟨z.val, hzD⟩ = y := by
      apply Subtype.ext
      change c ((A.chart j).symm z.val) = y.val
      rw [← heq]
      exact c.right_inv y.property
    exact ⟨hzD, by rwa [hFy]⟩
  · rintro ⟨hzD, hy⟩
    have hiS : (A.chart j).symm z.val ∈ c.source := by
      change z.val ∈ ((A.chart j).symm.trans c).source at hzD
      rw [OpenPartialHomeomorph.trans_source] at hzD
      exact hzD.2
    refine ⟨holomorphicDomainMap hFD ⟨z.val, hzD⟩, hy, ?_⟩
    change c.symm (c ((A.chart j).symm z.val)) = (A.chart j).symm z.val
    exact c.left_inv hiS

/-- Actual original atlas charts are particular genuine compatible coordinates. -/
theorem isOpen_plurifine_chartInverse_image (A : VariableComplexAtlas X) (i : A.Index)
    {V : Set (A.chartDomain i)} (hV : IsOpen[domainPlurifineTopology (A.chartDomain i)] V) :
    IsOpen[A.plurifineTopology] ((A.chartInverse i) '' V) :=
  A.isOpen_plurifine_coordinateInverse_image (A.chart i) (fun j ↦ A.holomorphic j i) hV

/-- Actual original fine-coordinate images, with genuine varying dimensions. -/
def plurifineChartBasis (A : VariableComplexAtlas X) : Set (Set X) :=
  {S | ∃ (i : A.Index) (V : Set (A.chartDomain i)),
    IsOpen[domainPlurifineTopology (A.chartDomain i)] V ∧ S = (A.chartInverse i) '' V}

/-- The whole original fine-coordinate family is a genuine topological basis
of the independently constructed fine manifold topology. -/
theorem plurifineChartBasis_isTopologicalBasis (A : VariableComplexAtlas X) :
    @IsTopologicalBasis X A.plurifineTopology A.plurifineChartBasis := by
  apply @isTopologicalBasis_of_isOpen_of_nhds X A.plurifineTopology A.plurifineChartBasis
  · rintro S ⟨i, V, hV, rfl⟩
    exact A.isOpen_plurifine_chartInverse_image i hV
  · intro x S hx hS
    obtain ⟨i, hi⟩ := A.cover x
    let V := (A.chartInverse i) ⁻¹' S
    have hV : IsOpen[domainPlurifineTopology (A.chartDomain i)] V :=
      (A.isOpen_plurifine_iff S).mp hS i
    let z : A.chartDomain i := ⟨(A.chart i) x, (A.chart i).map_source hi⟩
    have hz : A.chartInverse i z = x := (A.chart i).left_inv hi
    refine ⟨(A.chartInverse i) '' V, ⟨i, V, hV, rfl⟩, ⟨z, ?_, hz⟩, image_preimage_subset _ _⟩
    change A.chartInverse i z ∈ S
    rwa [hz]

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.PSH.VariableComplexAtlas
open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X]

/-- Actual holomorphic overlap derivatives in both coordinate directions. -/
structure CompatibleCoordinate (A : VariableComplexAtlas X) {d : ℕ}
    (c : OpenPartialHomeomorph X (ComplexModel d)) : Prop where
  forward : ∀ i, DifferentiableOn ℂ ((A.chart i).symm.trans c)
    ((A.chart i).symm.trans c).source
  backward : ∀ i, DifferentiableOn ℂ (c.symm.trans (A.chart i))
    (c.symm.trans (A.chart i)).source

/-- Original charts satisfy the actual two-sided compatibility condition. -/
theorem compatibleCoordinate_chart (A : VariableComplexAtlas X) (i : A.Index) :
    CompatibleCoordinate A (A.chart i) :=
  ⟨fun j ↦ A.holomorphic j i, fun j ↦ A.holomorphic i j⟩

/-- Restrict a genuine coordinate map to an actual ordinary-open target. -/
noncomputable def restrictedCoordinate {d : ℕ}
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (B : Set (ComplexModel d)) (hB : IsOpen B) :
    OpenPartialHomeomorph X (ComplexModel d) :=
  c.trans (OpenPartialHomeomorph.ofSet B hB)

@[simp] theorem restrictedCoordinate_apply {d : ℕ}
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (B : Set (ComplexModel d)) (hB : IsOpen B) (x : X) :
    restrictedCoordinate c B hB x = c x := rfl

@[simp] theorem restrictedCoordinate_symm_apply {d : ℕ}
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (B : Set (ComplexModel d)) (hB : IsOpen B) (z : ComplexModel d) :
    (restrictedCoordinate c B hB).symm z = c.symm z := rfl

/-- The actual target after restriction is the original chosen open subset. -/
theorem restrictedCoordinate_target {d : ℕ}
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (B : Set (ComplexModel d)) (hB : IsOpen B) (hBc : B ⊆ c.target) :
    (restrictedCoordinate c B hB).target = B := by
  change B ∩ c.target = B
  exact inter_eq_left.mpr hBc

/-- Restriction retains genuine holomorphic overlap derivatives in both
directions; fine continuity is a conclusion, never a compatibility field. -/
theorem CompatibleCoordinate.restricted {A : VariableComplexAtlas X} {d : ℕ}
    {c : OpenPartialHomeomorph X (ComplexModel d)} (hc : CompatibleCoordinate A c)
    (B : Set (ComplexModel d)) (hB : IsOpen B) :
    CompatibleCoordinate A (restrictedCoordinate c B hB) := by
  constructor
  · intro i
    have hsub : ((A.chart i).symm.trans (restrictedCoordinate c B hB)).source ⊆
        ((A.chart i).symm.trans c).source := by
      intro z hz
      rw [OpenPartialHomeomorph.trans_source] at hz ⊢
      refine ⟨hz.1, ?_⟩
      have hzc := hz.2
      change (A.chart i).symm z ∈ c.source ∩ c ⁻¹' B at hzc
      exact hzc.1
    exact (hc.forward i).mono hsub
  · intro i
    have hsub : ((restrictedCoordinate c B hB).symm.trans (A.chart i)).source ⊆
        (c.symm.trans (A.chart i)).source := by
      intro z hz
      rw [OpenPartialHomeomorph.trans_source] at hz ⊢
      refine ⟨?_, hz.2⟩
      have hzB := hz.1
      change z ∈ B ∩ c.target at hzB
      exact hzB.2
    exact (hc.backward i).mono hsub

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.PSH.VariableComplexAtlas
open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology
universe u
variable {X : Type u} [TopologicalSpace X]

/-- The source family uses every genuine compatible biholomorphic coordinate
map with an actual connected nonempty target, in every coordinate dimension. -/
def sourcePlurifineCoordinateBasis (A : VariableComplexAtlas X) : Set (Set X) :=
  {S | ∃ (d : ℕ) (c : OpenPartialHomeomorph X (ComplexModel d)),
    CompatibleCoordinate A c ∧ IsConnected c.target ∧
      ∃ V : Set (coordinateDomain c),
        IsOpen[domainPlurifineTopology (coordinateDomain c)] V ∧
          S = (coordinateInverse c) '' V}

/-- Every member of the original all-coordinate source family is actually
open in the independently defined manifold topology. -/
theorem sourcePlurifineCoordinateBasis_isOpen (A : VariableComplexAtlas X)
    {S : Set X} (hS : S ∈ A.sourcePlurifineCoordinateBasis) :
    IsOpen[A.plurifineTopology] S := by
  obtain ⟨d, c, hc, _, V, hV, rfl⟩ := hS
  exact A.isOpen_plurifine_coordinateInverse_image c hc.forward hV

/-- Connected coordinate targets are produced by actual positive-radius
balls. Thus the exact whole source family, rather than only original atlas
charts, is a genuine basis of the independently defined topology. -/
theorem sourcePlurifineCoordinateBasis_isTopologicalBasis (A : VariableComplexAtlas X) :
    @IsTopologicalBasis X A.plurifineTopology A.sourcePlurifineCoordinateBasis := by
  apply @isTopologicalBasis_of_isOpen_of_nhds X A.plurifineTopology
    A.sourcePlurifineCoordinateBasis
  · intro S hS
    exact A.sourcePlurifineCoordinateBasis_isOpen hS
  · intro x S hx hS
    obtain ⟨i, hi⟩ := A.cover x
    let z := (A.chart i) x
    have hz : z ∈ (A.chart i).target := (A.chart i).map_source hi
    obtain ⟨r, hr, hBall⟩ := Metric.isOpen_iff.mp (A.chart i).open_target z hz
    let c := restrictedCoordinate (A.chart i) (Metric.ball z r) Metric.isOpen_ball
    have hct : c.target = Metric.ball z r :=
      restrictedCoordinate_target (A.chart i) _ _ hBall
    have hc : CompatibleCoordinate A c :=
      (A.compatibleCoordinate_chart i).restricted _ _
    have hconn : IsConnected c.target := by
      rw [hct]
      exact Metric.isConnected_ball hr
    have hinc : (coordinateDomain c : Set (ComplexModel (A.dimension i))) ⊆
        A.chartDomain i := by
      intro w hw
      apply hBall
      change w ∈ c.target at hw
      rwa [hct] at hw
    let ι := holomorphicDomainMap (F := id) hinc
    let V := (A.chartInverse i) ⁻¹' S
    have hV : IsOpen[domainPlurifineTopology (A.chartDomain i)] V :=
      (A.isOpen_plurifine_iff S).mp hS i
    let W := ι ⁻¹' V
    have hW : IsOpen[domainPlurifineTopology (coordinateDomain c)] W :=
      isOpen_domainPlurifine_preimage_holomorphic differentiable_id.differentiableOn hinc hV
    have hzc : z ∈ c.target := by
      rw [hct]
      exact Metric.mem_ball_self hr
    let z' : coordinateDomain c := ⟨z, hzc⟩
    have hinv : coordinateInverse c z' = x := (A.chart i).left_inv hi
    refine ⟨(coordinateInverse c) '' W,
      ⟨A.dimension i, c, hc, hconn, W, hW, rfl⟩, ⟨z', ?_, hinv⟩, ?_⟩
    · change (A.chart i).symm z ∈ S
      change (A.chart i).symm ((A.chart i) x) ∈ S
      rwa [(A.chart i).left_inv hi]
    · rintro y ⟨w, hw, rfl⟩
      exact hw

end SGPT.PSH.VariableComplexAtlas

namespace SGPT.PSH.VariableComplexAtlas
open Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology

/-- A genuine open Euclidean domain has its actual global inclusion chart. -/
noncomputable def domainAtlas {n : ℕ} (Ω : Opens (ComplexModel n)) (hne : Nonempty Ω) :
    VariableComplexAtlas Ω where
  Index := Unit
  dimension := fun _ ↦ n
  chart := fun _ ↦ Ω.openPartialHomeomorphSubtypeCoe hne
  cover := fun x ↦ ⟨(), by simp⟩
  holomorphic := fun _ _ ↦ by
    let e := Ω.openPartialHomeomorphSubtypeCoe hne
    apply (differentiable_id : Differentiable ℂ
      (id : ComplexModel n → ComplexModel n)).differentiableOn.congr
    intro z hz
    change e (e.symm z) = z
    apply e.right_inv
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact hz.1

/-- The genuine global domain chart has exactly the original open target. -/
theorem chartDomain_domainAtlas {n : ℕ} (Ω : Opens (ComplexModel n)) (hne : Nonempty Ω) :
    (domainAtlas Ω hne).chartDomain () = Ω := by
  apply Opens.ext
  exact Ω.openPartialHomeomorphSubtypeCoe_target hne

/-- The independently defined manifold fine topology of the genuine domain
atlas agrees with the original PSH initial topology of that domain. -/
theorem plurifineTopology_domainAtlas {n : ℕ} (Ω : Opens (ComplexModel n))
    (hne : Nonempty Ω) :
    (domainAtlas Ω hne).plurifineTopology = domainPlurifineTopology Ω := by
  let A := domainAtlas Ω hne
  let D : Opens (ComplexModel n) :=
    ⟨(Ω.openPartialHomeomorphSubtypeCoe hne).target,
      (Ω.openPartialHomeomorphSubtypeCoe hne).open_target⟩
  have hD : D = Ω := by
    apply Opens.ext
    exact Ω.openPartialHomeomorphSubtypeCoe_target hne
  have hinc : (D : Set (ComplexModel n)) ⊆ (Ω : Set (ComplexModel n)) := by
    rw [hD]
  have hrev : (Ω : Set (ComplexModel n)) ⊆
      (D : Set (ComplexModel n)) := by
    rw [hD]
  let ι := holomorphicDomainMap (F := id) hinc
  let ρ := holomorphicDomainMap (F := id) hrev
  have hInv : A.chartInverse () = ι := by
    funext z
    apply Subtype.ext
    change ((Ω.openPartialHomeomorphSubtypeCoe hne).symm z.val).val = z.val
    have h := (Ω.openPartialHomeomorphSubtypeCoe hne).right_inv z.property
    exact h
  apply le_antisymm
  · intro S hS
    apply (A.isOpen_plurifine_iff S).mpr
    intro i
    cases i
    rw [hInv]
    exact isOpen_domainPlurifine_preimage_holomorphic differentiable_id.differentiableOn hinc hS
  · intro S hS
    have hU := (A.isOpen_plurifine_iff S).mp hS ()
    have hUi : IsOpen[domainPlurifineTopology D] (ι ⁻¹' S) := hInv ▸ hU
    have h := isOpen_domainPlurifine_preimage_holomorphic
      differentiable_id.differentiableOn hrev hUi
    change IsOpen[domainPlurifineTopology Ω] S at h
    exact h

end SGPT.PSH.VariableComplexAtlas
