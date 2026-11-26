/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.PathWalkEquivalences
public import LeanPool.GraphMinor.Statement
import LeanPool.GraphMinor.GM16.GraphIsoEdgeEnds

/-!
# Matching paths by their walk positions

Two spanning simple walks of equal length enumerate their graph
vertices and edges in the same order. Match positions to construct
bijections. Consecutive positions preserve the ends of every edge,
so these bijections form an isomorphism taking the first and last
vertices to the corresponding ends. This is used to draw each
subdivision path on its prescribed line in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Surface
universe u v u' v'

/-- Spanning simple walks of the same length give an isomorphism
matching both ends in their stated order. -/
theorem exists_iso_of_spanning_path_walks
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {P : Graph α β} {Q : Graph α' β'} {a b : α} {a' b' : α'}
    (W : GraphWalk P a b) (W' : GraphWalk Q a' b') (hW : W.IsSimple) (hW' : W'.IsSimple)
    (hV : V(P) = {x | x ∈ W.support}) (hE : E(P) = {e | e ∈ W.edges})
    (hV' : V(Q) = {x | x ∈ W'.support}) (hE' : E(Q) = {e | e ∈ W'.edges})
    (hLen : W.length = W'.length) :
    ∃ φ : Iso P Q, (∀ x : V(P), x.val=a → (φ.vertexEquiv x).val=a') ∧
      (∀ x : V(P), x.val=b → (φ.vertexEquiv x).val=b') := by
  obtain ⟨vp,hvp⟩ := exists_pathWalk_vertexEquiv W hW hV
  obtain ⟨vq,hvq⟩ := exists_pathWalk_vertexEquiv W' hW' hV'
  obtain ⟨ep,hep⟩ := exists_pathWalk_edgeEquiv W hW hE
  obtain ⟨eq,heq⟩ := exists_pathWalk_edgeEquiv W' hW' hE'
  let vq' : Fin (W.length+1) ≃ V(Q) := (finCongr (congrArg (fun n => n+1) hLen)).trans vq
  let eq' : Fin W.length ≃ E(Q) := (finCongr hLen).trans eq
  have hvq' (i : Fin (W.length+1)) :
      (vq' i).val = pathWalkVertex W' i.val (by omega) := hvq _
  have heq' (i : Fin W.length) :
      (eq' i).val = pathWalkEdge W' i.val (by omega) := heq _
  let fv := vp.symm.trans vq'
  let fe := ep.symm.trans eq'
  have hVMap (i : Fin (W.length+1)) : fv (vp i) = vq' i := by
    change vq' (vp.symm (vp i)) = vq' i
    rw [vp.symm_apply_apply]
  have hEnds (e : E(P)) : ∃ x y : V(P), P.IsLink e.val x.val y.val ∧
      Q.IsLink (fe e).val (fv x).val (fv y).val := by
    let k := ep.symm e
    let i₀ : Fin (W.length+1) := ⟨k.val,by omega⟩
    let i₁ : Fin (W.length+1) := ⟨k.val+1,by omega⟩
    refine ⟨vp i₀,vp i₁,?_,?_⟩
    · have h := pathWalkEdge_isLink W k.val k.isLt
      rw [← hep k,← hvp i₀,← hvp i₁] at h
      simpa only [k,Equiv.apply_symm_apply] using h
    · have hEdge : (fe e).val = pathWalkEdge W' k.val (by omega) := heq' k
      rw [hEdge,hVMap,hVMap,hvq',hvq']
      exact pathWalkEdge_isLink W' k.val (by omega)
  let φ : Iso P Q := ⟨fv,fe,isLink_iff_of_edge_ends fv fe hEnds⟩
  refine ⟨φ,?_,?_⟩
  · intro x hx
    let i : Fin (W.length+1) := ⟨0,by omega⟩
    have hpi : (vp i).val=a := (hvp i).trans (pathWalkVertex_zero W)
    have hxi : x=vp i := Subtype.ext (hx.trans hpi.symm)
    rw [hxi]
    change (fv (vp i)).val=a'
    rw [hVMap,hvq']
    exact pathWalkVertex_zero W'
  · intro x hx
    let i : Fin (W.length+1) := ⟨W.length,by omega⟩
    have hpi : (vp i).val=b := (hvp i).trans (pathWalkVertex_last W)
    have hxi : x=vp i := Subtype.ext (hx.trans hpi.symm)
    rw [hxi]
    change (fv (vp i)).val=b'
    rw [hVMap,hvq']
    simpa only [i,hLen] using pathWalkVertex_last W'

end GraphMinor.GM16
