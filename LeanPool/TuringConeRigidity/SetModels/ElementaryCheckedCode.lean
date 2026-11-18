/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementaryCheckedCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.ParameterCoveringModels
public import LeanPool.TuringConeRigidity.SetModels.ElementaryDefinableSets

/-!
# Elementary Checked Code
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SentenceForm
universe u

theorem ambient_transitive_container (x : ZFSet.{u}) :
    ∃ d : ZFSet.{u}, TransitiveNameModel.Transitive d ∧ x ∈ d := by
  let b := ZFSet.range (fun n : ℕ => iterUnion n x)
  let d := ({x} : ZFSet.{u}) ∪ ZFSet.sUnion b
  refine ⟨d,?_,ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_singleton.mpr rfl))⟩
  intro y hy z hz
  apply ZFSet.mem_union.mpr
  apply Or.inr
  rcases ZFSet.mem_union.mp hy with hy|hy
  · have hyx : y = x := ZFSet.mem_singleton.mp hy
    subst y
    exact ZFSet.mem_sUnion.mpr ⟨x,ZFSet.mem_range.mpr ⟨0,rfl⟩,hz⟩
  · obtain ⟨c,hc,hyc⟩ := ZFSet.mem_sUnion.mp hy
    obtain ⟨n,rfl⟩ := ZFSet.mem_range.mp hc
    exact ZFSet.mem_sUnion.mpr ⟨iterUnion (n+1) x,ZFSet.mem_range.mpr ⟨n+1,rfl⟩,
      ZFSet.mem_sUnion.mpr ⟨y,hyc,hz⟩⟩

theorem ambient_checkGraph (d t : ZFSet.{u}) (hd : Transitive d) :
    ∃ r f, CheckGraph d r f t := by
  let f := ZFSet.range (fun i : Conditions d => ZFSet.pair (label d i) (checkedCode t (label d i)))
  refine ⟨iterUnion 2 f,f,checkGraph_of_mem_iff d f t hd ?_⟩
  intro z
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨label d i,label_mem d i,hi.symm⟩
  · rintro ⟨x,hx,hz⟩
    obtain ⟨i,rfl⟩ := label_surjective d hx
    exact ⟨i,hz.symm⟩

/-- A full formula selecting the value of a checked name through its coded graph. -/
noncomputable def checkedValueFormula : SentenceForm :=
  .ex (.ex (.ex (fromBounded (.conj (CheckFormula.graph 2 1 0 5)
    (.conj (.member 4 2) (.conj (.member 3 1) (.pairMem 4 3 0)))))))

theorem checkedValue_univ (v x t : ZFSet.{u}) :
    checkedValueFormula.Sat Set.univ (cons v (cons x (fun _ => t))) ↔ v = checkedCode t x := by
  simp only [checkedValueFormula,Sat,bounded_univ,Formula.Eval,CheckFormula.eval_graph,
    Formula.eval_pairMem,cons_zero,cons_succ,Set.mem_univ,true_and]
  constructor
  · rintro ⟨d,r,f,hg,hx,hv,hf⟩
    exact hg.correct x hx v hv hf
  · intro hv
    obtain ⟨d,hd,hx⟩ := ambient_transitive_container x
    obtain ⟨r,f,hg⟩ := ambient_checkGraph d t hd
    obtain ⟨w,hw,hf,_⟩ := hg.2.2.1 x hx
    have he : w = v := (hg.correct x hx w hw hf).trans hv.symm
    exact ⟨d,r,f,hg,hx,he ▸ hw,he ▸ hf⟩

theorem checkedValue_sound (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (h : checkedValueFormula.Sat (M : Set ZFSet) e) : e 0 = checkedCode (e 2) (e 1) := by
  obtain ⟨d,hd,r,hr,f,hf,h⟩ := h
  have hi : ∀ i, cons f (cons r (cons d e)) i ∈ M := by
    intro i; rcases i with _|_|_|i
    · exact hf
    · exact hr
    · exact hd
    · exact he i
  rw [bounded_sat,Formula.absolute _ M hM _ hi] at h
  simp only [Formula.Eval,CheckFormula.eval_graph,Formula.eval_pairMem,cons_zero,cons_succ] at h
  exact h.1.correct (e 1) h.2.1 (e 0) h.2.2.1 h.2.2.2

theorem checkedCode_mem_hull (a : ℕ → ZFSet.{u}) {t x : ZFSet.{u}}
    (ht : t ∈ hullSet a) (hx : x ∈ hullSet a) : checkedCode t x ∈ hullSet a := by
  exact unique_definable_mem a checkedValueFormula (cons x (fun _ => t))
    (by intro i; cases i <;> assumption) _ ((checkedValue_univ _ x t).mpr rfl)
    (fun v hv => (checkedValue_univ v x t).mp hv)

theorem collapse_checkedCode (a : ℕ → ZFSet.{u}) {t x : ZFSet.{u}}
    (ht : t ∈ hullSet a) (hx : x ∈ hullSet a) :
    structureMap (hullSet a) (checkedCode t x) =
      checkedCode (structureMap (hullSet a) t) (structureMap (hullSet a) x) := by
  let e := cons (checkedCode t x) (cons x (fun _ => t))
  have he : ∀ i, e i ∈ hullSet a := by
    intro i; rcases i with _|_|i
    · exact checkedCode_mem_hull a ht hx
    · exact hx
    · exact ht
  have hs := (collapsed_hull_elementary a checkedValueFormula e he).mpr
    ((checkedValue_univ _ x t).mpr rfl)
  exact checkedValue_sound _ (collapsed_transitive _) _
    (fun i => (mem_collapsed _ _).mpr ⟨e i,he i,rfl⟩) hs

theorem collapse_encoded_check (a : ℕ → ZFSet.{u})
    {c c' : ZFSet.{u}} [Top (Conditions c)] [Top (Conditions c')]
    (ht : label c ⊤ ∈ hullSet a)
    (ht' : structureMap (hullSet a) (label c ⊤) = label c' ⊤)
    {x : ZFSet.{u}} (hx : x ∈ hullSet a) :
    structureMap (hullSet a) ((RecursiveNames.Name.check x).encode (label c)) =
      (RecursiveNames.Name.check (structureMap (hullSet a) x)).encode (label c') := by
  rw [encode_check,encode_check,collapse_checkedCode a ht hx,ht']

end TuringRigidity.ElementaryModel

end OAI
