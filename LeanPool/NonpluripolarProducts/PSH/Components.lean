/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.LocalManifold
public import LeanPool.NonpluripolarProducts.PSH.Choquet

/-! Exact source open-domain agreement and product over the actual components. -/

@[expose] public section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Metric
open SGPT.Foundations.Analysis.FirstPass

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Equal representatives on the actual subset have identical source witnesses. -/
theorem IsPSHOn.congr {u v : X → EReal} {U : Set X}
    (hu : A.IsPSHOn u U) (heq : EqOn u v U) : A.IsPSHOn v U := by
  intro x hx
  obtain ⟨i, hi, V, hV, hc, hVe, hxV, huV⟩ := hu x hx
  have he : EqOn (A.coordinate u i) (A.coordinate v i) V :=
    fun z hz ↦ heq (hVe hz).2
  obtain ⟨z, hz, hn⟩ := huV.nontrivial
  exact ⟨i, hi, V, hV, hc, hVe, hxV, huV.disc.congr he,
    z, hz, by rwa [← he hz]⟩

/-- Restrict to an actual open subset using the existing finite-point producer. -/
theorem IsPSHOn.mono_open {u : X → EReal} {U V : Set X}
    (hu : A.IsPSHOn u U) (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) :
    A.IsPSHOn u V := by
  apply (isPSHOn_iff_chart_and_nondegenerate hV).mpr
  refine ⟨fun i ↦ (hu.chartPlurisubharmonic i).mono (fun z hz ↦ ⟨hz.1, hVU hz.2⟩), ?_⟩
  intro x hx O hO hxO
  obtain ⟨y, hy, hn⟩ := hu.locallyNondegenerate hU x (hVU hx)
    (V ∩ O) (hV.inter hO) ⟨hx, hxO⟩
  exact ⟨y, hy.2, hn⟩

/-- The genuine identity coordinate atlas, including dimension zero. -/
noncomputable def identityAtlas (n : ℕ) : VariableComplexAtlas (ComplexModel n) where
  Index := Unit
  dimension := fun _ ↦ n
  chart := fun _ ↦ OpenPartialHomeomorph.refl (ComplexModel n)
  cover := fun _ ↦ ⟨(), mem_univ _⟩
  holomorphic := fun _ _ ↦ by
    simpa using (differentiable_id : Differentiable ℂ (id : ComplexModel n → ComplexModel
      n)).differentiableOn

/-- SGPT ex:pshfunctions:L172: the actual open connected domain and source
manifold-neighborhood definitions coincide, with the non-bottom clause retained. -/
theorem identityAtlas_isPSHOn_iff {n : ℕ} {u : ComplexModel n → EReal}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hc : IsConnected U) :
    (identityAtlas n).IsPSHOn u U ↔ PSHOn u U := by
  constructor
  · intro hu
    exact hu.coordinate_pshOn_of_connected hU () hU hc (fun z hz ↦ ⟨mem_univ z, hz⟩)
  · intro hu x hx
    exact ⟨(), mem_univ _, U, hU, hc, fun z hz ↦ ⟨mem_univ z, hz⟩, hx, hu⟩

/-- Extend an actual function on a subset; its outside values are irrelevant. -/
noncomputable def extendByZero {U : Set X} (u : U → EReal) : X → EReal :=
  by
    classical
    exact fun x ↦ if hx : x ∈ U then u ⟨x, hx⟩ else 0

omit [TopologicalSpace X] in
theorem extendByZero_apply_of_mem {U : Set X} (u : U → EReal) {x : X} (hx : x ∈ U) :
    extendByZero u x = u ⟨x, hx⟩ := by simp [extendByZero, hx]

/-- Actual functions on the actual open subset, tested by the exact local
source predicate. Equal ambient representatives give the same class by congr. -/
def PSHSpaceOn (A : VariableComplexAtlas X) (U : Set X) :=
  {u : U → EReal // A.IsPSHOn (extendByZero u) U}

/-- The actual source index set of connected components. -/
def Components (X : Type*) [TopologicalSpace X] := range (connectedComponent : X → Set X)

/-- The connected component of the manifold containing the point. -/
def componentOf (x : X) : Components X := ⟨connectedComponent x, mem_range_self x⟩

theorem componentOf_eq {c : Components X} {x : X} (hx : x ∈ c.val) :
    componentOf x = c := by
  obtain ⟨y, hy⟩ := c.property
  apply Subtype.ext
  change connectedComponent x = c.val
  rw [← hy]
  exact (connectedComponent_eq (hy ▸ hx)).symm

theorem isOpen_actual_component (A : VariableComplexAtlas X) (c : Components X) :
    IsOpen c.val := by
  obtain ⟨x, hx⟩ := c.property
  rw [← hx]
  exact A.isOpen_component x

/-- Genuine source functions restrict to the actual component function space. -/
noncomputable def restrictToComponents (A : VariableComplexAtlas X)
    (u : {u : X → EReal // A.IsPSH u}) (c : Components X) : PSHSpaceOn A c.val := by
  refine ⟨fun x ↦ u.val x, ?_⟩
  have hu := (isPSHOn_univ_iff.mpr u.property).mono_open isOpen_univ
    (A.isOpen_actual_component c) (subset_univ _)
  apply hu.congr
  intro x hx
  exact (extendByZero_apply_of_mem (fun y : c.val ↦ u.val y) hx).symm

/-- Glue the actual component functions at their original manifold points. -/
noncomputable def glueComponents (v : (c : Components X) → PSHSpaceOn A c.val) : X → EReal :=
  fun x ↦ (v (componentOf x)).val ⟨x, mem_connectedComponent⟩

theorem glueComponents_eqOn (v : (c : Components X) → PSHSpaceOn A c.val)
    (c : Components X) : EqOn (extendByZero (v c).val) (glueComponents v) c.val := by
  intro x hx
  rw [extendByZero_apply_of_mem _ hx]
  have heq := componentOf_eq hx
  subst c
  rfl

/-- Local witnesses of the actual components glue to genuine source witnesses
at every original point, with no countability or nonempty-space assumption. -/
theorem isPSH_glueComponents (v : (c : Components X) → PSHSpaceOn A c.val) :
    A.IsPSH (glueComponents v) := by
  intro x
  have hu := ((v (componentOf x)).property).congr (glueComponents_eqOn v (componentOf x))
  obtain ⟨i, hi, V, hV, hc, hVe, hxV, hw⟩ := hu x mem_connectedComponent
  exact ⟨i, hi, V, hV, hc, fun z hz ↦ (hVe hz).1, hxV, hw⟩

/-- SGPT ex:pshfunctions:L176: the canonical bijection of actual functions,
over the actual connected components. No countable-component assumption. -/
noncomputable def componentProductEquiv (A : VariableComplexAtlas X) :
    {u : X → EReal // A.IsPSH u} ≃ ((c : Components X) → PSHSpaceOn A c.val) where
  toFun := restrictToComponents A
  invFun v := ⟨glueComponents v, isPSH_glueComponents v⟩
  left_inv u := by
    apply Subtype.ext
    funext x
    rfl
  right_inv v := by
    funext c
    apply Subtype.ext
    funext x
    change glueComponents v x.val = (v c).val x
    rw [← glueComponents_eqOn v c x.property, extendByZero_apply_of_mem _ x.property]

/-- The exact source empty-manifold function space is a singleton. -/
noncomputable instance emptyPSHSpaceUnique (A : VariableComplexAtlas X) [IsEmpty X] :
    Unique {u : X → EReal // A.IsPSH u} where
  default := ⟨fun _ ↦ 0, fun x ↦ isEmptyElim x⟩
  uniq _u := Subtype.ext (funext fun x ↦ isEmptyElim x)

end SGPT.PSH.VariableComplexAtlas
