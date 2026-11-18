/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/FullSetTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.FullSetForcing
public import LeanPool.TuringConeRigidity.SetModels.ElementarySchemas

/-!
# Full Set Truth
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
open ElementaryModel SentenceForm BoundedForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

/-- Conditions deciding the full sentence or its negation relative to the model's name codes. -/
def Decision (M : ZFSet.{u}) (e : ℕ → Name (Conditions c)) (φ : SentenceForm) : Set (Conditions c)
  :=
  {p | Forces M e φ p ∨ Forces M e (.neg φ) p}

theorem decision_dense (M : ZFSet.{u}) (e : ℕ → Name (Conditions c)) (φ : SentenceForm) :
    Dense (Decision M e φ) := by
  classical
  intro p
  by_cases h : ∃ q, q ≤ p ∧ Forces M e φ q
  · obtain ⟨q,hqp,hq⟩ := h; exact ⟨q,hqp,Or.inl hq⟩
  · exact ⟨p,le_rfl,Or.inr (fun q hq hf => h ⟨q,hq,hf⟩)⟩

theorem internal_decision (M : ZFSet.{u}) (hM : Transitive M) (hV : Valid M)
    (hc : c ∈ M) {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SentenceForm) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M) :
    ∃ D ∈ M, ∀ q, label c q ∈ D ↔ q ∈ Decision M e φ := by
  let env := cons c (cons o (fun i => (e i).encode (label c)))
  have henv : ∀ i, env i ∈ M := by
    intro i
    rcases i with _|_|i
    · exact hc
    · exact hoM
    · exact he i
  let ψ := disj (code φ 1 2 0 (fun i => i+3)) (code (.neg φ) 1 2 0 (fun i => i+3))
  obtain ⟨D,hD,hdef⟩ := hV.separate ψ env henv c hc
  refine ⟨D,hD,?_⟩
  intro q
  have hqm := hM c hc _ (label_mem c q)
  have sub (χ : SentenceForm) := realize_code M hM (hV.sourceT hM ⟨c,hc⟩) ho χ e q
    (cons (label c q) env) (by
      intro i
      cases i
      · exact hqm
      · exact henv _)
    1 2 0 (fun i => i+3) rfl rfl rfl (fun _ => rfl)
  rw [hdef _ hqm]
  simp only [label_mem c q,true_and,ψ,sat_disj,sub]
  rfl

theorem full_truth (M : ZFSet.{u}) (hM : Transitive M) (hV : Valid M)
    (hc : c ∈ M) {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (φ : SentenceForm) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M) :
    φ.Sat (genericExtensionSet M c G.carrier : Set ZFSet) (fun i => (e i).val G.carrier) ↔
      ∃ p ∈ G.carrier, Forces M e φ p := by
  have hT := hV.sourceT hM ⟨c,hc⟩
  have hS := hT.separation.finitePrefix.bounded
  have hR := hT.replacement.finitePrefix
  induction φ generalizing e with
  | equal i j =>
    exact BoundedForcing.internal_bounded_truth M hM hT.pairing hT.union hT.powerSet hS hR
      hT.infinity
      hc hoM ho G hG (.equal i j) e he
  | member i j =>
    exact BoundedForcing.internal_bounded_truth M hM hT.pairing hT.union hT.powerSet hS hR
      hT.infinity
      hc hoM ho G hG (.member i j) e he
  | conj φ ψ ihφ ihψ =>
    constructor
    · rintro ⟨hφ,hψ⟩
      obtain ⟨p,hp,hφ⟩ := (ihφ e he).mp hφ
      obtain ⟨q,hq,hψ⟩ := (ihψ e he).mp hψ
      obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
      exact ⟨r,hr,forces_mono M φ e hrp hφ,forces_mono M ψ e hrq hψ⟩
    · rintro ⟨p,hp,hφ,hψ⟩
      exact ⟨(ihφ e he).mpr ⟨p,hp,hφ⟩,(ihψ e he).mpr ⟨p,hp,hψ⟩⟩
  | neg φ ih =>
    constructor
    · intro hn
      obtain ⟨D,hD,hdef⟩ := internal_decision M hM hV hc hoM ho φ e he
      have hd : Dense {q | label c q ∈ D} := by
        intro p; obtain ⟨q,hq,hf⟩ := decision_dense M e φ p
        exact ⟨q,hq,(hdef q).mpr hf⟩
      obtain ⟨p,hp,hpd⟩ := hG D hD hd
      rcases (hdef p).mp hpd with hf|hf
      · exact False.elim (hn ((ih e he).mpr ⟨p,hp,hf⟩))
      · exact ⟨p,hp,hf⟩
    · rintro ⟨p,hp,hf⟩ htruth
      obtain ⟨q,hq,hqf⟩ := (ih e he).mp htruth
      obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
      exact hf r hrp (forces_mono M φ e hrq hqf)
  | ex φ ih =>
    have hep (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :
        ∀ i, (push a e i).encode (label c) ∈ M := by
      intro i
      cases i
      · exact ha
      · exact he _
    have env (a : Name (Conditions c)) : (fun i => (push a e i).val G.carrier) =
        cons (a.val G.carrier) (fun i => (e i).val G.carrier) := by funext i; cases i <;> rfl
    constructor
    · rintro ⟨x,hx,hφ⟩
      obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
      rw [←env a] at hφ
      obtain ⟨p,hp,hf⟩ := (ih _ (hep a ha)).mp hφ
      exact ⟨p,hp,a,ha,hf⟩
    · rintro ⟨p,hp,a,ha,hf⟩
      refine ⟨a.val G.carrier,(mem_extensionSet M c G.carrier _).mpr ⟨a,ha,rfl⟩,?_⟩
      rw [←env a]
      exact (ih _ (hep a ha)).mpr ⟨p,hp,hf⟩

end TuringRigidity.FullSetForcing

end OAI
