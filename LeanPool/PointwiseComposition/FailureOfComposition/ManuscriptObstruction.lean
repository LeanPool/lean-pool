/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteWeakTotality

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The four conclusions of manuscript Theorem 1, retaining uniform provable
equality in its two middle clauses. The concrete productive witnesses have
these uniform graph equations already in PA, before passing to the theory T.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition
namespace ConcreteIndices

open ProofSearch ConcreteEvaluator HistoryWitnesses ProgramIndices ConcreteEmptyGraph

/-- Uniform equality of the concrete arithmetic program graphs. -/
def UniformIndex (T : ArithmeticTheory) (e f : ℕ) : Prop :=
  Uniform T (eventualGraph e) (eventualGraph f)

/-- The manuscript's Kleene equality formula, universally quantified over inputs. -/
def uniformKleeneSentence (F G : Graph) : ArithmeticSentence :=
  “∀ x,
      ((∃ y, !F.val x y) ↔ (∃ y, !G.val x y)) ∧
        ((∃ y, !F.val x y) → ∃ y, !F.val x y ∧ !G.val x y)”

@[simp]
theorem uniformKleeneSentence_eval {M : Type*} [ORingStructure M] (F G : Graph) :
    (uniformKleeneSentence F G).Evalb (M := M) ![] ↔
      ∀ x : M,
        ((∃ y, F.val.Evalb ![x, y]) ↔ ∃ y, G.val.Evalb ![x, y]) ∧
          ((∃ y, F.val.Evalb ![x, y]) → ∃ y, F.val.Evalb ![x, y] ∧ G.val.Evalb ![x, y]) :=
  by simp [uniformKleeneSentence]

/-!
The implication from output-graph equality to Kleene equality is pure
first-order logic.  The explicit LK construction below deliberately avoids the
converse direction, functionality, PA, semantic completeness, and the later
`uniformKleeneSentence_iff_uniformSentence`. -/

private theorem implication_context (a b : ArithmeticProposition)
    (h : Nonempty (LK.Derivation ⦃a ⇒ₗ b⦄)) : Nonempty (LK.Derivation (⦃∼a⦄ + ⦃b⦄)) :=
  by
  rcases h with ⟨d⟩
  have dn : LK.Derivation (⦃∼a⦄ + ⦃b⦄ + ⦃∼(a ⇒ₗ b)⦄) := by
    refine
      LK.Derivation.cast
        (LK.Derivation.tensor (Γ := ⦃∼a⦄) (Δ := ⦃b⦄) (φ := a) (ψ := ∼b)
          (Multiset.Traversal.atom _) (Multiset.Traversal.atom _)
          ((LK.Derivation.eta a).cast (by simp [add_comm])) (LK.Derivation.eta b))
        (by simp [Semiformula.imp_eq, add_comm, add_assoc])
  refine
    ⟨LK.Derivation.cast
        (LK.Derivation.cut (Γ := 0) (Δ := ⦃∼a⦄ + ⦃b⦄) (φ := a ⇒ₗ b)
          (LK.Derivation.cast d (by simp)) dn)
        (by simp)⟩

private theorem all_imp_all (p q : ArithmeticSemiformula ℕ 1)
    (h : Nonempty (LK.Derivation ⦃p.free ⇒ₗ q.free⦄)) :
    Nonempty (LK.Derivation ⦃(∀¹ p) ⇒ₗ (∀¹ q)⦄) :=
  by
  rcases implication_context p.free q.free h with ⟨d⟩
  refine ⟨?_⟩
  refine
    LK.Derivation.cast (LK.Derivation.or (Γ := 0) (φ := ∼(∀¹ p)) (ψ := ∀¹ q) ?_)
      (by simp [Semiformula.imp_eq])
  refine LK.Derivation.cast (LK.Derivation.all (Γ := ⦃∼(∀¹ p)⦄) (φ := q) ?_) (by simp)
  refine
    LK.Derivation.cast
      (LK.Derivation.exs (Γ := ⦃q.free⦄) (φ := (∼p).shift) (t := &0)
        (LK.Derivation.cast d (by simp [Semiformula.free, add_comm])))
      (by simp [Rewriting.shifts, Semiformula.free, add_comm])

private theorem implication_core (p q : ArithmeticSemiformula ℕ 1) :
    Nonempty (LK.Derivation (⦃(∼p).free⦄ + ⦃q.free⦄ + ⦃(∼(p ⇒ₗ q)).free⦄)) :=
  by
  refine ⟨?_⟩
  refine
    LK.Derivation.cast
      (LK.Derivation.tensor (Γ := ⦃(∼p).free⦄) (Δ := ⦃q.free⦄) (φ := p.free) (ψ := ∼q.free)
        (Multiset.Traversal.atom _) (Multiset.Traversal.atom _)
        ((LK.Derivation.eta p.free).cast (by simp [Semiformula.free, add_comm]))
        (LK.Derivation.eta q.free))
      (by simp [Semiformula.free, Semiformula.imp_eq, add_comm, add_assoc])

private theorem implication_exs_right (p q : ArithmeticSemiformula ℕ 1) :
    Nonempty (LK.Derivation (⦃(∼p).free⦄ + ⦃(∼(p ⇒ₗ q)).free⦄ + ⦃∃¹ q.shift⦄)) :=
  by
  rcases implication_core p q with ⟨d⟩
  refine
    ⟨LK.Derivation.cast
        (LK.Derivation.exs (Γ := ⦃(∼p).free⦄ + ⦃(∼(p ⇒ₗ q)).free⦄) (φ := q.shift) (t := &0)
          (LK.Derivation.cast d (by simp [Semiformula.free, add_comm, add_assoc])))
        (by simp [add_assoc])⟩

private theorem implication_exs_both (p q : ArithmeticSemiformula ℕ 1) :
    Nonempty (LK.Derivation (⦃(∼p).free⦄ + ⦃∃¹ q.shift⦄ + ⦃∃¹ (∼(p ⇒ₗ q)).shift⦄)) :=
  by
  rcases implication_exs_right p q with ⟨d⟩
  refine
    ⟨LK.Derivation.cast
        (LK.Derivation.exs (Γ := ⦃(∼p).free⦄ + ⦃∃¹ q.shift⦄) (φ := (∼(p ⇒ₗ q)).shift) (t := &0)
          (LK.Derivation.cast d
            (by simp [Semiformula.free, add_comm, add_left_comm, add_assoc])))
        (by simp [add_assoc])⟩

private theorem all_imp_exs (p q : ArithmeticSemiformula ℕ 1) :
    Nonempty (LK.Derivation ⦃(∀¹ (p ⇒ₗ q)) ⇒ₗ ((∃¹ p) ⇒ₗ (∃¹ q))⦄) :=
  by
  rcases implication_exs_both p q with ⟨d⟩
  refine ⟨?_⟩
  refine
    LK.Derivation.cast
      (LK.Derivation.or (L := ℒₒᵣ) (Γ := 0) (φ := ∼(∀¹ (p ⇒ₗ q))) (ψ := (∃¹ p) ⇒ₗ (∃¹ q)) ?_)
      (by simp [Semiformula.imp_eq])
  refine
    LK.Derivation.cast
      (LK.Derivation.or (L := ℒₒᵣ) (Γ := ⦃∼(∀¹ (p ⇒ₗ q))⦄) (φ := ∼(∃¹ p)) (ψ := ∃¹ q) ?_)
      (by simp [Semiformula.imp_eq])
  refine
    LK.Derivation.cast (LK.Derivation.all (Γ := ⦃∼(∀¹ (p ⇒ₗ q)), ∃¹ q⦄) (φ := ∼p) ?_)
      (by simp [add_comm, add_left_comm, add_assoc])
  exact LK.Derivation.cast d (by simp [Rewriting.shifts, Semiformula.free, add_comm, add_assoc])

private theorem uniform_one (p q : ArithmeticSemiformula ℕ 1) :
    Nonempty (LK.Derivation ⦃(∀¹ (p ⇔ₗ q)) ⇒ₗ (((∃¹ p) ⇔ₗ (∃¹ q)) ⋏ ((∃¹ p) ⇒ₗ ∃¹ (p ⋏ q)))⦄) :=
  by
  have hpq₀ : Nonempty (LK.Derivation ⦃(p.free ⇔ₗ q.free) ⇒ₗ (p.free ⇒ₗ q.free)⦄) :=
    by
    change (𝐋𝐊¹ : FFL.FirstOrder.LK ℒₒᵣ) ⊢ (p.free ⇔ₗ q.free) ⇒ₗ (p.free ⇒ₗ q.free)
    cl_prover
  have hpq : Nonempty (LK.Derivation ⦃(p ⇔ₗ q).free ⇒ₗ (p ⇒ₗ q).free⦄) := by
    simpa [Semiformula.free] using hpq₀
  have hqp₀ : Nonempty (LK.Derivation ⦃(p.free ⇔ₗ q.free) ⇒ₗ (q.free ⇒ₗ p.free)⦄) :=
    by
    change (𝐋𝐊¹ : FFL.FirstOrder.LK ℒₒᵣ) ⊢ (p.free ⇔ₗ q.free) ⇒ₗ (q.free ⇒ₗ p.free)
    cl_prover
  have hqp : Nonempty (LK.Derivation ⦃(p ⇔ₗ q).free ⇒ₗ (q ⇒ₗ p).free⦄) := by
    simpa [Semiformula.free] using hqp₀
  have hconj₀ :
    Nonempty (LK.Derivation ⦃(p.free ⇔ₗ q.free) ⇒ₗ (p.free ⇒ₗ (p.free ⋏ q.free))⦄) :=
    by
    change (𝐋𝐊¹ : FFL.FirstOrder.LK ℒₒᵣ) ⊢ (p.free ⇔ₗ q.free) ⇒ₗ (p.free ⇒ₗ (p.free ⋏ q.free))
    cl_prover
  have hconj : Nonempty (LK.Derivation ⦃(p ⇔ₗ q).free ⇒ₗ (p ⇒ₗ (p ⋏ q)).free⦄) := by
    simpa [Semiformula.free] using hconj₀
  have hallPQ : (𝐋𝐊¹ : FFL.FirstOrder.LK ℒₒᵣ) ⊢ (∀¹ (p ⇔ₗ q)) ⇒ₗ ∀¹ (p ⇒ₗ q) :=
    all_imp_all (p ⇔ₗ q) (p ⇒ₗ q) hpq
  have hallQP : (𝐋𝐊¹ : FFL.FirstOrder.LK ℒₒᵣ) ⊢ (∀¹ (p ⇔ₗ q)) ⇒ₗ ∀¹ (q ⇒ₗ p) :=
    all_imp_all (p ⇔ₗ q) (q ⇒ₗ p) hqp
  have hallConj : (𝐋𝐊¹ : FFL.FirstOrder.LK ℒₒᵣ) ⊢ (∀¹ (p ⇔ₗ q)) ⇒ₗ ∀¹ (p ⇒ₗ (p ⋏ q)) :=
    all_imp_all (p ⇔ₗ q) (p ⇒ₗ (p ⋏ q)) hconj
  have hexPQ : (𝐋𝐊¹ : FFL.FirstOrder.LK ℒₒᵣ) ⊢ (∀¹ (p ⇒ₗ q)) ⇒ₗ ((∃¹ p) ⇒ₗ (∃¹ q)) :=
    all_imp_exs p q
  have hexQP : (𝐋𝐊¹ : FFL.FirstOrder.LK ℒₒᵣ) ⊢ (∀¹ (q ⇒ₗ p)) ⇒ₗ ((∃¹ q) ⇒ₗ (∃¹ p)) :=
    all_imp_exs q p
  have hexConj :
    (𝐋𝐊¹ : FFL.FirstOrder.LK ℒₒᵣ) ⊢ (∀¹ (p ⇒ₗ (p ⋏ q))) ⇒ₗ ((∃¹ p) ⇒ₗ ∃¹ (p ⋏ q)) :=
    all_imp_exs p (p ⋏ q)
  change
    (𝐋𝐊¹ : FFL.FirstOrder.LK ℒₒᵣ) ⊢
      (∀¹ (p ⇔ₗ q)) ⇒ₗ (((∃¹ p) ⇔ₗ (∃¹ q)) ⋏ ((∃¹ p) ⇒ₗ ∃¹ (p ⋏ q)))
  cl_prover[hallPQ, hallQP, hallConj, hexPQ, hexQP, hexConj]

/-- Pure LK proves that an internally universal graph biconditional implies
the manuscript's internally universal Kleene-equality sentence. -/
theorem uniformSentence_imp_uniformKleeneSentence (F G : Graph) :
    (∅ : ArithmeticTheory) ⊢ uniformSentence F G ⇒ₗ uniformKleeneSentence F G :=
  by
  let p : ArithmeticSemiformula ℕ 1 :=
    Rewriting.free ((Rewriting.emb F.val : ArithmeticSemiformula ℕ 2).subst ![#1, #0])
  let q : ArithmeticSemiformula ℕ 1 :=
    Rewriting.free ((Rewriting.emb G.val : ArithmeticSemiformula ℕ 2).subst ![#1, #0])
  let source : ArithmeticSemiproposition 1 := “x. ∀ y, !F.val x y ↔ !G.val x y”
  let target : ArithmeticSemiproposition 1 :=
    “x.
      ((∃ y, !F.val x y) ↔ (∃ y, !G.val x y)) ∧
        ((∃ y, !F.val x y) → ∃ y, !F.val x y ∧ !G.val x y)”
  have hone₀ := uniform_one p q
  have hone : Nonempty (LK.Derivation ⦃source.free ⇒ₗ target.free⦄) := by
    simpa [source, target, p, q, Semiformula.free] using hone₀
  have hall := all_imp_all source target hone
  apply FFL.FirstOrder.Theory.Proof.of_LK_provable
  rcases hall with ⟨d⟩
  refine ⟨LK.Derivation.cast d ?_⟩
  simp [uniformSentence, uniformKleeneSentence, source, target,
    Semiformula.coe_subst_eq_subst_coe, Matrix.fun_eq_vec_two]

/-- The one direction needed by the obstruction transport, over any theory. -/
theorem uniformKleeneSentence_of_uniformSentence (T : ArithmeticTheory) (F G : Graph)
    (h : T ⊢ uniformSentence F G) : T ⊢ uniformKleeneSentence F G :=
  by
  have himp : T ⊢ uniformSentence F G ⇒ₗ uniformKleeneSentence F G :=
    Entailment.wkProof (by simp) (uniformSentence_imp_uniformKleeneSentence F G)
  exact himp⨀h

/-- PA functionality equates the two uniform encodings, at all internal inputs. -/
theorem uniformKleeneSentence_iff_uniformSentence (F G : Graph) (hF : Functional F)
    (hG : Functional G) : 𝐏𝐀 ⊢ uniformKleeneSentence F G ⇔ₗ uniformSentence F G :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have hf := consequence_iff.mp (Theory.Proof.sound hF) M inferInstance
  have hg := consequence_iff.mp (Theory.Proof.sound hG) M inferInstance
  simp only [models_iff, functionalSentence_eval] at hf hg
  simp only [models_iff, LogicalConnective.HomClass.map_iff, uniformKleeneSentence_eval,
    uniformSentence_eval, LogicalConnective.Prop.iff_eq]
  apply forall_congr'
  intro x
  constructor
  · rintro ⟨hdom, hcommon⟩ y
    constructor
    · intro hy
      obtain ⟨z, hzF, hzG⟩ := hcommon ⟨y, hy⟩
      exact (hf x y z hy hzF).symm ▸ hzG
    · intro hy
      obtain ⟨z, hzF, hzG⟩ := hcommon (hdom.mpr ⟨y, hy⟩)
      exact (hg x y z hy hzG).symm ▸ hzF
  · intro h
    exact ⟨exists_congr h, fun ⟨y, hy⟩ => ⟨y, hy, (h y).mp hy⟩⟩

/-- UniformIndex is precisely provability of the manuscript's uniform formula. -/
theorem uniformIndex_iff_kleene (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (e f : ℕ) :
    UniformIndex T e f ↔ T ⊢ uniformKleeneSentence (eventualGraph e) (eventualGraph f) :=
  by
  have h :
    T ⊢
      uniformKleeneSentence (eventualGraph e) (eventualGraph f) ⇔ₗ
        uniformSentence (eventualGraph e) (eventualGraph f) :=
    WeakerThan.pbl
      (uniformKleeneSentence_iff_uniformSentence _ _ (eventualGraph_functional e)
        (eventualGraph_functional f))
  constructor
  · intro he
    have he' : T ⊢ uniformSentence (eventualGraph e) (eventualGraph f) := he
    cl_prover[h, he']
  · intro he
    change T ⊢ uniformSentence (eventualGraph e) (eventualGraph f)
    cl_prover[h, he]

private theorem uniform_trans {F G H : Graph} (hFG : Uniform 𝐏𝐀 F G) (hGH : Uniform 𝐏𝐀 G H) :
    Uniform 𝐏𝐀 F H := by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have hFG' := consequence_iff.mp (Theory.Proof.sound hFG) M inferInstance
  have hGH' := consequence_iff.mp (Theory.Proof.sound hGH) M inferInstance
  simp only [models_iff, uniformSentence_eval] at hFG' hGH' ⊢
  exact fun x y => (hFG' x y).trans (hGH' x y)

private theorem uniform_symm {F G : Graph} (hFG : Uniform 𝐏𝐀 F G) : Uniform 𝐏𝐀 G F :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have hFG' := consequence_iff.mp (Theory.Proof.sound hFG) M inferInstance
  simp only [models_iff, uniformSentence_eval] at hFG' ⊢
  exact fun x y => (hFG' x y).symm

/-- The concrete identity law is uniformly provable already in PA. -/
theorem identity_comp_uniformIndex (e : ℕ) :
    UniformIndex 𝐏𝐀 (canonicalPartrecCompIndex Kleene.identityIndex e) e :=
  by
  have hRefl : Uniform 𝐏𝐀 (eventualGraph e) (eventualGraph e) :=
    by
    apply complete.{0} 𝐏𝐀
    intro M _ _
    simp [models_iff, uniformSentence_eval]
  exact
    uniform_trans (eventualGraph_composition _ _)
      (uniform_trans (uniform_comp eventualGraph_identity hRefl)
        (identity_comp (eventualGraph e)))

/-- The guard-search composite has uniformly empty graph already in PA. -/
theorem guard_search_uniformIndex_empty (d : ℕ) :
    UniformIndex 𝐏𝐀 (canonicalPartrecCompIndex (guardIndex d) (searchIndex d))
      concreteEmptyIndex :=
  uniform_trans (eventualGraph_composition _ _)
    (uniform_trans (uniform_comp (guardIndex_realizes d) (searchIndex_realizes d))
      (uniform_trans (HistoryWitnesses.guard_search_empty d)
        (uniform_symm eventualGraph_empty)))

/-- The four manuscript properties, with the stronger PA-uniform middle clauses. -/
theorem index_four_witnesses_uniform_of_history_divergence (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (d : ℕ) (hdiv : ¬diagonalHistoryFormula.Evalb ![d])
    (hnot : T ⊬ ∼diagonalHistoryFormula/[d]) :
    PointwiseIndex T (guardIndex d) Kleene.identityIndex ∧
      UniformIndex 𝐏𝐀 (canonicalPartrecCompIndex (guardIndex d) (searchIndex d))
          concreteEmptyIndex ∧
        UniformIndex 𝐏𝐀 (canonicalPartrecCompIndex Kleene.identityIndex (searchIndex d))
            (searchIndex d) ∧
          ¬PointwiseIndex T (searchIndex d) concreteEmptyIndex :=
  ⟨guardIndex_pointwise_identity T d hdiv, guard_search_uniformIndex_empty d,
    identity_comp_uniformIndex (searchIndex d), searchIndex_not_pointwise_empty T d hnot⟩

/-- Theorem 1's four properties for every consistent recursively axiomatized
extension of PA. Uniform provability is retained, not replaced by its instances. -/
theorem obstruction_four_properties_of_re_axioms (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T]
    (hT : REPred (AxiomCodes T)) :
    ∃ f g : ℕ,
      PointwiseIndex T f Kleene.identityIndex ∧
        UniformIndex T (canonicalPartrecCompIndex f g) concreteEmptyIndex ∧
          UniformIndex T (canonicalPartrecCompIndex Kleene.identityIndex g) g ∧
            ¬PointwiseIndex T g concreteEmptyIndex :=
  by
  obtain ⟨d, hdiv, hnot⟩ :=
    exists_true_unprovable_history_divergence_of_theorem_codes T
      (theorem_codes_re_of_axiom_codes T hT)
  obtain ⟨hfi, hfg, hig, hgz⟩ :=
    index_four_witnesses_uniform_of_history_divergence T d hdiv hnot
  exact ⟨guardIndex d, searchIndex d, hfi, WeakerThan.pbl hfg, WeakerThan.pbl hig, hgz⟩

/-- The explicit partial-recursive axiom-enumerator presentation of Theorem 1. -/
theorem obstruction_four_properties_of_axiom_enumerator (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    [Consistent T] (a : ℕ) (ha : ∀ n : ℕ, AxiomCodes T n ↔ ∃ x : ℕ, n ∈ Kleene.eval a x) :
    ∃ f g : ℕ,
      PointwiseIndex T f Kleene.identityIndex ∧
        UniformIndex T (canonicalPartrecCompIndex f g) concreteEmptyIndex ∧
          UniformIndex T (canonicalPartrecCompIndex Kleene.identityIndex g) g ∧
            ¬PointwiseIndex T g concreteEmptyIndex :=
  obstruction_four_properties_of_re_axioms T (axiom_codes_re_of_program_enumerator T a ha)

end ConcreteIndices
end FailureOfComposition

end

end PointwiseComposition
