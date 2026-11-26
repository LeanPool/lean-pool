/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.General.Ballot
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Geometry.Exterior
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Panel.Shapes
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Waves.Price
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.General.Scales
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Waves.Scenario
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access

/-! # Occupied-cell indices for printed profiles -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local

private theorem retype_none {α β : Type} (h : α = β) :
    cast (congrArg Option h) (none : Option α) = none := by cases h; rfl

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {h g ℓ D T b d p l j : ℕ} {W : ℝ} {S : Scheme F}
    (P : Input F x y h D T (d * b) g W)
    {z : S.format.obj} (A : P.HostChart S z)
    (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
    (s : P.Occupied → Shape (probes ℓ D) b d)

local notation "world" => P.localWorld A sc hK s
local notation "Cfg" => design S g ℓ D b d p l

theorem printMenu_away {menu : (Cfg).Menu F (B S.k) (B S.ℓ) j} (c : (world).Code (Cfg).waves menu)
    {M r t : ℕ} (ha : d * b = M * r) (hb : d = M * t) (v : B S.m × B S.h) (hv : v ∉ Set.range
      A.coord) :
    printMenu S menu ha hb ((c.tape v.1).2 v.2) = none := by
  unfold printMenu
  rw [P.panel_read A sc hK s c v, (world).atlas.fill_away _ hv]
  exact retype_none (congrArg₂ (fun x y => Print.Face F x y (Cfg).R (panelKeys Cfg) (B S.k)) ha hb)

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input

namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer.NamedRelease
open Coloring Assembly Rounds

variable {F K J : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F}
  {d ℓ M r t q D k n u j z T R g σ : ℕ} {W : ℝ} {P : Input F x y S.h D T R g W}
  {tape : S.format.obj} {U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z}
  {pres : S.Presentation tape P.diagram} {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  {f : Val x → Val y → F} (o : U.NamedRelease pres data status f σ)
  (loc : J ↪ B S.m × B S.h)
  (vacant : ∀ v ∉ Set.range loc, U.menu ((data v.1).2 v.2) = none)

include vacant

/-- Even if the printed tensor vanishes, the explicit profile still
has a unit scalar and has only the padding ballot at vacant cells. -/
theorem supported (i : o.I) : Sparse.Supported loc U.pad (o.select.write i) := by
  apply U.supported data _ loc vacant
  rw [o.valid, (o.select.valid _ i).mpr rfl, Option.elim_some]
  exact o.nonzero i

/-- Computes the local index by the application `Sparse.compress loc U.pad o.select (o.supported
loc vacant)`. -/
def localIndex := Sparse.compress loc U.pad o.select (o.supported loc vacant)

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer.NamedRelease
end

/- # Initial records with a mobility rule depending on the local label and seat -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere.Surface.Local SphereScale Transcript Finset

variable {F K : Type} [Field F] [Field K] [Algebra K F] {g ℓ D T b d p l : ℕ}

section
variable (S : Scheme F)

local notation "Cfg" => design S g ℓ D b d p l
local notation "Query" => panelQuery S g ℓ D b d p l

open scoped Classical in
/-- Unused seats contribute no stations. A cell may have several fixed
stations when the mobility rule is false on several occupied seats. -/
def localMenu (hK : Ready K ℓ D g (p ^ l) b d) (mobility : B S.ℓ → B S.k → Bool) (k : ℕ) :
    (Cfg).Menu F (B S.k) (B S.ℓ) (Query k).width := fun j =>
  let v := (Design.number (Query k)).symm j
  if live S v.1.1 then
    if h : v.1.2.2.2.val < Fintype.card (Shape (probes ℓ D) b d) then
      viewStart S hK v.1.1 v.1.2.1 v.1.2.2.1 (fun i => (v.2 i).1) (fun i => (v.2 i).2.1)
        (mobility v.1.1) ((Fintype.equivFin _).symm ⟨_, h⟩)
    else (v.1.1, none)
  else (v.1.1, none)

end

variable {x y : Wire} {h k : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W) {S : Scheme F} {z : S.format.obj}
  (A : P.HostChart S z) (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
  (s : P.Occupied → Shape (probes ℓ D) b d) {t : S.Presentation z P.diagram}
  {mobility : B S.ℓ → B S.k → Bool}
  (H : P.Placed t A.coord (fun i => (A.tone (2 * D ^ 5 + 2) i).val) (fun v
    => mobility ((z v.1).2 v.2.1) v.2.2))

local notation "Sh" => Shape (probes ℓ D) b d

include H

open scoped Classical in
theorem localWeight (hk : initialChoices ℓ D b d ≤ 2 ^ k) (c : (Boot.selectors S.m S.h k).obj) :
    Fmt.weight (panelGuard S sc k) (panelAround S sc z c) =
      ((P.panelSelector A hk).read c).elim 0 (fun _ => 1) := by
  let w (v : B S.m × B S.h) := panelGuard S sc k (((panelAround S sc z c) v.1).2 v.2)
  have fits : Fintype.card Sh ≤ 2 ^ k := by rw [card_shape]; exact hk
  have hw := Selector.scattered_weight A.coord (fun _ => Sh) (fun _ => fits)
    (Function.uncurry c) (fun _ _ => (1 : F)) w (by
      intro j
      have hj := (H.live_iff (A.coord j)).mpr ⟨j, rfl⟩
      simp only [w, panelGuard, panelAround, Boot.around, Boot.colored, hj, ite_true,
        Function.uncurry]
      split_ifs <;> rfl)
    (by
      intro v hv
      have hv' := mt (H.live_iff v).mp hv
      simp only [w, panelGuard, panelAround, Boot.around, Boot.colored, hv', ite_false,
        Function.uncurry]
      split_ifs <;> rfl)
  simp only [prod_const_one, Fintype.prod_prod_type] at hw
  exact hw

open scoped Classical in
/-- The physical tape and the initial frame agree at every host, including vacant slots. -/
def localCode (hr : P.LocalRanks) (hk : initialChoices ℓ D b d ≤ 2 ^ k) :
    (P.localWorld A sc hK s).Code 0 (localMenu S hK mobility k) where
  frame := P.start A sc hK s
  tape := panelTape S sc z ((P.panelSelector A hk).write s)
  host _ := rfl
  read := by
    intro i
    simp only [panelTape, Fmt.update, localMenu, Equiv.symm_apply_apply, panelAround, Boot.around,
      Boot.colored]
    by_cases hi : i ∈ Set.range A.coord
    · obtain ⟨j, rfl⟩ := hi
      have hj := (H.live_iff (A.coord j)).mpr ⟨j, rfl⟩
      simp only [hj, ite_true, P.panelSelector_at, Fin.is_lt, ↓reduceDIte, Fin.eta,
        Equiv.symm_apply_apply]
      exact (P.start_at A sc hK s H hr j).symm
    · rw [ite_eq_right (mt (H.live_iff i).mp hi)]
      exact (P.start_away A sc hK s i hi).symm

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
end

/- # Occupied-cell selectors for initialization and motion -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Transcript

variable {F : Type} {x y : Wire} {g ℓ D T b d p l h k : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W) {S : Scheme F} {z : S.format.obj}
  (A : P.HostChart S z) (hk : initialChoices ℓ D b d ≤ 2 ^ k)

theorem panel_supported (i : P.Occupied → Shape (probes ℓ D) b d) :
    Sparse.Supported A.coord 0 ((P.panelSelector A hk).write i) :=
  fun v hv => Selector.scatter_away A.coord _ (fun _ => by rw [card_shape]; exact hk) i v hv

/-- Computes the local index by the application `Sparse.compress A.coord 0 (P.panelSelector A
hk) (P.panel_supported A hk)`. -/
def localIndex := Sparse.compress A.coord 0 (P.panelSelector A hk) (P.panel_supported A hk)

variable [Field F] (sc : Scales g ℓ D T (p ^ l) b d)
  {t : S.Presentation z P.diagram} {mobility : B S.ℓ → B S.k → Bool}
  (H : P.Placed t A.coord (fun i => (A.tone (2 * D ^ 5 + 2) i).val) (fun v
    => mobility ((z v.1).2 v.2.1) v.2.2))

include H hk in
theorem guard_supported (c : (Boot.selectors S.m S.h k).obj)
    (hc : Fmt.weight (panelGuard S sc k) (panelAround S sc z c) ≠ 0) :
    Sparse.Supported A.coord 0 c := by
  rw [P.localWeight A sc H hk] at hc
  exact Sparse.of_weight A.coord 0 _ (P.panel_supported A hk) hc

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input

namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
open Coloring Assembly

variable {F A N : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p]
  {e k : ℕ} {x y : Wire} {menu : a.Menu F N A e}
  (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (j : Fin a.waves) (s : w.Code j.val menu)
  (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)

/-- Computes the local index by the application `Sparse.compress w.atlas.coord 0 (w.selector hF
j s hk) (w.selector_away hF j s hk)`. -/
def localIndex := Sparse.compress w.atlas.coord 0 (w.selector hF j s hk) (w.selector_away hF j s hk)

include hk in
theorem weight_supported (c : (a.selectors k).obj)
    (hc : Fmt.weight (a.tariff hF j menu k) (a.around s.tape c) ≠ 0) :
    Sparse.Supported w.atlas.coord 0 c := by
  rw [w.weighted hF j s hk] at hc
  exact Sparse.of_weight w.atlas.coord 0 _ (w.selector_away hF j s hk) hc

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
end

/- # Computing the weight from the occupied occurrences alone -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent
open Coloring Assembly Sphere

namespace Rounds.Input
open SphereScale
variable {F : Type} [Field F] {x y : Wire} {h k g ℓ D T b d p l : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W) {S : Scheme F} {z : S.format.obj}
  (A : P.HostChart S z) (sc : Scales g ℓ D T (p ^ l) b d)
  {pres : S.Presentation z P.diagram} {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}

open scoped Classical in
theorem guard_occupied (H : P.Placed pres A.coord tone mobile) (c : P.Occupied → B k) :
    let t := panelAround S sc z (Sparse.pack A.coord 0 c)
    Fmt.weight (panelGuard S sc k) t =
      ∏ i, panelGuard S sc k ((t (A.coord i).1).2 (A.coord i).2) := by
  intro t
  refine Sparse.prod_occupied A.coord (fun v => panelGuard S sc k ((t v.1).2 v.2)) ?_
  intro v hv
  have empty := mt (H.live_iff v).mp hv
  have zero := Sparse.pack_supported A.coord 0 c v hv
  simp only [t, panelGuard, panelAround, Boot.around, Boot.colored, empty, ite_false, zero,
    ite_true]

end Rounds.Input

namespace Sphere.Surface.Local.Scenario
variable {F N A : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p] {x y : Wire}
  (w : Scenario F N A a x y) {e k : ℕ} (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (menu : a.Menu F N A e) (start : w.Code 0 menu)

open scoped Classical in
theorem charge_occupied (i : ℕ) (hi : i ≤ a.waves) (c : w.History k i) :
    a.totalCharge start.tape hF menu i hi (w.tapes c) =
      ∏ v, a.localCharge start.tape hF menu i hi (w.tapes c) (w.atlas.coord v) := by
  refine a.total_occupied start.tape hF menu w.atlas.coord ?_ i hi (w.tapes c)
    (fun j => Sparse.pack_supported _ _ (c j))
  intro v hv
  rw [start.read, stored, Palette.records_away _ _ _ _ _ hv]

end Sphere.Surface.Local.Scenario

namespace Sphere.Print.Printer
variable {F K N : Type} [Field F] {m d h e M r t q D k n u j z : ℕ}
  (U : Printer F K N m d h e M r t q D k n u j z) (data : U.rows.obj)

open scoped Classical in
theorem score_occupied {J : Type} [Fintype J] (loc : J ↪ B m × B h)
    (vacant : ∀ v ∉ Set.range loc, U.menu ((data v.1).2 v.2) = none) (c : J → B U.digits) :
    U.score data (Sparse.pack loc U.pad c) =
      ∏ v, U.tariff (((U.around data (Sparse.pack loc U.pad c)) (loc v).1).2 (loc v).2) := by
  let tape := Sparse.pack loc U.pad c
  refine Sparse.prod_occupied loc (fun v => U.tariff (((U.around data tape) v.1).2 v.2)) ?_
  intro v hv
  let w := U.view (((U.around data tape) v.1).2 v.2)
  have he : w 0 0 = (none, fun _ _ => 0) := by
    have padAt : tape v.1 v.2 = U.pad := Sparse.pack_supported loc U.pad c v hv
    simp only [w, view, around, Fmt.around, Fmt.expand, Fmt.zip, Neighborhood.origin, vacant v hv,
      padAt, pad, Equiv.symm_apply_apply]
  have ok : w.valid U.positive := by simp [Lens.valid, Lens.ask, he, quota, tally]
  change w.score U.positive = 1
  simp [Lens.score, ok, he]

end Sphere.Print.Printer
end MatrixMultiplicationAllFields.MatrixExponent
end

/- # A finite expansion indexed by the occupied-cell history -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
open Assembly Coloring Transcript Finset

variable {F N A : Type} [Field F] [Fintype F] {x y : Wire} {a : Design} [ExpChar F a.p]
    (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
    {e : ℕ} (menu : a.Menu F N A e) (k : ℕ) (start : w.Code 0 menu)

open scoped Classical in
/-- The condition `∀ i, w.History k i → w.At i → Prop` on the specified data. -/
abbrev Invariant := ∀ i, w.History k i → w.At i → Prop

open scoped Classical in
/-- Computes the at code by the application `w.Code i (a.menuAt hF menu k i hi)`. -/
abbrev AtCode (i : ℕ) (hi : i ≤ a.waves) := w.Code i (a.menuAt hF menu k i hi)

open scoped Classical in
/-- Every accepted branch has a tape and a semantic frame. Validity
also accounts for the weights of words outside the branch index. -/
structure Run (Good : w.Invariant k) (i : ℕ) (hi : i ≤ a.waves) where
  /-- The `Run` component of type `Type`. -/
  I : Type
  [finite : Fintype I]
  /-- The `Run` component of type `Selector I (w.History k i)`. -/
  select : Selector I (w.History k i)
  /-- The `Run` component of type `I → F`. -/
  coeff : I → F
  /-- The encoding map carried by `Run`, with type `I → w.AtCode hF menu k i hi`. -/
  code : I → w.AtCode hF menu k i hi
  good : ∀ j, Good i (select.write j) (code j).frame
  written : ∀ j, (code j).tape = a.path start.tape i (w.tapes (select.write j))
  valid : ∀ c, a.totalCharge start.tape hF menu i hi (w.tapes c) = (select.read c).elim 0 coeff
  value : ∀ u v, w.eval start.frame u v = ∑ j, coeff j * w.eval (code j).frame u v

attribute [instance] Run.finite

open scoped Classical in
/-- The only extension rule needed of a semantic invariant. -/
def Extends (Good : w.Invariant k) (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k) : Prop
    :=
  ∀ (j : Fin a.waves) (c : w.History k j.val) (s : w.AtCode hF menu k j.val j.isLt.le),
    s.tape = a.path start.tape j.val (w.tapes c) → Good j.val c s.frame →
    ∃ q : w.Branch hF j s → w.AtCode hF menu k (j.val + 1) j.isLt,
      (∀ t, (q t).tape = a.update s.tape ((w.selector hF j s hk).write t)) ∧
      (∀ t, Good (j.val + 1) (Fin.snoc c ((w.localIndex hF j s hk).write t)) (q t).frame) ∧
      ∀ u v, w.eval s.frame u v = ∑ t, w.scalar hF j s t * w.eval (q t).frame u v

variable {Good : w.Invariant k}

open scoped Classical in
private def emptyIndex {X : Type} : Selector Unit (Fin 0 → X) where
  write _ := Fin.elim0
  read _ := some ()
  valid _ _ := ⟨fun _ => Subsingleton.elim _ _, fun _ => rfl⟩

open scoped Classical in
private def first (h : Good 0 Fin.elim0 start.frame) : w.Run hF menu k start Good 0 (Nat.zero_le _)
    where
  I := Unit
  select := emptyIndex
  coeff _ := 1
  code _ := start
  good _ := h
  written _ := rfl
  valid _ := rfl
  value u v := by simp only [one_mul, Fintype.sum_unique]

open scoped Classical in
private def snocIndex {X : Type} (i : ℕ) : ((Fin i → X) × X) ≃ (Fin (i + 1) → X) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => X)

variable (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)

open scoped Classical in
theorem path_write (j : Fin a.waves) (c : w.History k j.val) (s : w.AtCode hF menu k j.val
    j.isLt.le)
    (hc : s.tape = a.path start.tape j.val (w.tapes c)) (t : w.Branch hF j s) :
    a.path start.tape (j.val + 1) (w.tapes (Fin.snoc c ((w.localIndex hF j s hk).write t))) =
      a.update s.tape ((w.selector hF j s hk).write t) := by
  rw [tapes_snoc, Design.path_snoc, ← hc]
  exact congrArg (a.update s.tape) (Sparse.pack_sample _ _ (w.selector_away hF j s hk t))

open scoped Classical in
private theorem more (step : w.Extends hF menu k start Good hk) {i : ℕ} (hi : i < a.waves)
    (p : w.Run hF menu k start Good i hi.le) :
    Nonempty (w.Run hF menu k start Good (i + 1) hi) := by
  let j : Fin a.waves := ⟨i, hi⟩
  choose q ht hg hv using fun x => step j (p.select.write x) (p.code x) (p.written x) (p.good x)
  let S x := w.localIndex hF j (p.code x) hk
  let sel := (p.select.bind S).relabel (snocIndex i)
  let coeff (a : Σ x : p.I, w.Branch hF j (p.code x))
    := p.coeff a.1 * w.scalar hF j (p.code a.1) a.2
  refine ⟨{ I := Σ x, w.Branch hF j (p.code x)
            select := sel
            coeff := coeff
            code := fun x => q x.1 x.2
            good := fun x => hg x.1 x.2
            written := ?_
            valid := ?_
            value := ?_ }⟩
  · rintro ⟨x, t⟩
    exact (ht x t).trans (w.path_write hF menu k start hk j _ _ (p.written x) t).symm
  · intro c
    obtain ⟨⟨u, v⟩, rfl⟩ := (snocIndex i).surjective c
    simp only [sel, Selector.relabel, Equiv.symm_apply_apply]
    change a.totalCharge start.tape hF menu (i + 1) hi (w.tapes (Fin.snoc u v)) =
      ((p.select.read u).bind fun x => ((S x).read v).map (Sigma.mk x)).elim 0 coeff
    rw [tapes_snoc, Design.charge_snoc, p.valid]
    cases he : p.select.read u with
    | none => simp
    | some x =>
      have hu := (p.select.valid _ x).mp he
      rw [hu, ← p.written]
      have hw := w.weighted hF j (p.code x) hk (Sparse.pack w.atlas.coord 0 v)
      change _ = ((S x).read v).elim 0 _ at hw
      rw [hw]
      simp only [Option.bind_some, Option.elim_some]
      cases (S x).read v <;> simp [coeff]
  · intro u v
    rw [p.value, Fintype.sum_sigma]
    apply sum_congr rfl
    intro i _
    rw [hv, Finset.mul_sum]
    exact sum_congr rfl (fun j _ => (mul_assoc _ _ _).symm)

open scoped Classical in
theorem run (h : Good 0 Fin.elim0 start.frame) (step : w.Extends hF menu k start Good hk)
    (i : ℕ) (hi : i ≤ a.waves) : Nonempty (w.Run hF menu k start Good i hi) := by
  induction i with
  | zero => exact ⟨w.first hF menu k start h⟩
  | succ i ih => exact w.more hF menu k start hk step hi (ih (Nat.le_of_succ_le hi)).some

open scoped Classical in
theorem Run.card_le {i : ℕ} {hi : i ≤ a.waves} (p : w.Run hF menu k start Good i hi) :
    Fintype.card p.I ≤ 2 ^ (k * Fintype.card w.V * i) := by
  have h := Fintype.card_le_of_injective p.select.write p.select.injective
  simpa only [History, Fintype.card_fun, Fintype.card_fin, pow_mul] using h

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
end

/- # Certificates for the metadata at every prefix of a motion history -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
open Coloring

variable {F N A : Type} [Field F] [Fintype F] {x y : Wire} {a : Design} [ExpChar F a.p]
    (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
    {e : ℕ} (menu : a.Menu F N A e) (k : ℕ) (start : w.Code 0 menu)

/-- The value specified by `c ∘ Fin.castLE h`. -/
def before {X : Type} {i j : ℕ} (c : Fin i → X) (h : j ≤ i) : Fin j → X := c ∘ Fin.castLE h

@[simp] theorem before_self {X : Type} {i : ℕ} (c : Fin i → X) : before c le_rfl = c := rfl

theorem before_snoc {X : Type} {i j : ℕ} (c : Fin i → X) (t : X) (h : j ≤ i) :
    before (Fin.snoc c t) (h.trans (Nat.le_succ i)) = before c h := by
  funext l
  exact Fin.snoc_castSucc (α := fun _ => X) t c (Fin.castLE h l)

/-- Each consecutive pair of prefix tapes is realized by frames
satisfying the same regional energy and time inequalities. -/
def Certified : w.Invariant k := fun i c _ =>
  ∀ (j : Fin a.waves) (h : j.val < i),
    ∃ (p : w.AtCode hF menu k j.val j.isLt.le) (q : w.AtCode hF menu k (j.val + 1) j.isLt),
      p.tape = a.path start.tape j.val (w.tapes (before c h.le)) ∧
      q.tape = a.path start.tape (j.val + 1) (w.tapes (before c h)) ∧
      w.Balanced j p.frame q.frame

theorem certified_snoc (j : Fin a.waves) (c : w.History k j.val) (t : w.V → B k)
    (p : w.AtCode hF menu k j.val j.isLt.le) (q : w.AtCode hF menu k (j.val + 1) j.isLt)
    (hp : p.tape = a.path start.tape j.val (w.tapes c))
    (hq : q.tape = a.path start.tape (j.val + 1) (w.tapes (Fin.snoc c t)))
    (hb : w.Balanced j p.frame q.frame) (hc : w.Certified hF menu k start _ c p.frame) :
    w.Certified hF menu k start _ (Fin.snoc c t) q.frame := by
  intro l hl
  by_cases e : l = j
  · subst l
    rw [before_snoc c t le_rfl, before_self, before_self]
    exact ⟨p, q, hp, hq, hb⟩
  · have hlt : l.val < j.val := by
      have hne := Fin.val_injective.ne e
      omega
    rw [before_snoc c t hlt.le, before_snoc c t hlt]
    exact hc l hlt

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
end

/- # Regional balances throughout the occupied-cell expansion -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
open Coloring

variable {F N A : Type} [Field F] [Fintype F] {x y : Wire} {a : Design} [ExpChar F a.p]
    (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
    {e : ℕ} (menu : a.Menu F N A e) (k : ℕ) (start : w.Code 0 menu)
    (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)

/-- Computes the complete run by the application `w.Run hF menu k start (w.Certified hF menu k
start) a.waves le_rfl`. -/
abbrev CompleteRun := w.Run hF menu k start (w.Certified hF menu k start) a.waves le_rfl

include hk in
theorem run_balanced (hP : 0 < a.chart) (hH : 0 < a.H) : Nonempty (w.CompleteRun hF menu k start)
    := by
  apply w.run hF menu k start hk
  · intro j hj
    exact (Nat.not_lt_zero _ hj).elim
  · intro j c y hy hc
    obtain ⟨q, ht, hb, hv⟩ := w.step_balanced hF j y hk hP hH
    refine ⟨q, ht, fun i => ?_, hv⟩
    exact w.certified_snoc hF menu k start j c _ y (q i) hy
      ((ht i).trans (w.path_write hF menu k start hk j c y hy i).symm) (hb i) hc

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
end

/- # The three selector fields carried at each occupied cell -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local
open Coloring

open scoped Classical in
/-- Indexes the journal by the coordinates of `V → B k × (Fin w → B k) × B z`. -/
abbrev Journal (V : Type) (k w z : ℕ) := V → B k × (Fin w → B k) × B z

namespace Journal
variable {V : Type} {m h k w z : ℕ} (c : Journal V k w z) (loc : V ↪ B m × B h)

open scoped Classical in
/-- Reindexes `(V → B k) × (Fin w → V → B k) × (V → B z)` and `Journal V k w z where toFun t v`
by an equivalence. -/
def join : (V → B k) × (Fin w → V → B k) × (V → B z) ≃ Journal V k w z where
  toFun t v := (t.1 v, fun i => t.2.1 i v, t.2.2 v)
  invFun f := (fun v => (f v).1, fun i v => (f v).2.1 i, fun v => (f v).2.2)
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
/-- The indexed operation `Sparse.pack loc 0 (fun v => (c v).1)`. -/
def opening := Sparse.pack loc 0 (fun v => (c v).1)
open scoped Classical in
/-- The indexed operation `Sparse.pack loc 0 (fun v => (c v).2.1 i)`. -/
def moves (i : Fin w) := Sparse.pack loc 0 (fun v => (c v).2.1 i)
open scoped Classical in
/-- The indexed operation `Sparse.pack loc pad (fun v => (c v).2.2)`. -/
def close (pad : B z) := Sparse.pack loc pad (fun v => (c v).2.2)

open scoped Classical in
theorem card [Fintype V] : Fintype.card (Journal V k w z) = 2 ^ ((k + k * w + z) * Fintype.card V)
    := by
  simp only [Journal, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, pow_mul, pow_add,
    mul_assoc]

end Journal
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local

namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Assembly Coloring Sphere SphereScale Surface.Local
variable {F V : Type} [Field F] {g ℓ D T b d p l k f : ℕ} (S : Scheme F)
    (sc : Scales g ℓ D T (p ^ l) b d) (z : S.format.obj) (loc : V ↪ B S.m × B S.h)

local notation "Cfg" => design S g ℓ D b d p l
local notation "e" => Format.width (panelQuery S g ℓ D b d p l k)

/-- Deterministic tape after a given prefix of any journal. -/
def page (c : Journal V k (Cfg).waves f) (i : ℕ) (hi : i ≤ (Cfg).waves) :
    ((Cfg).port ((Cfg).widthAt e k i)).obj :=
  (Cfg).path (panelTape S sc z (c.opening loc)) i (Scenario.before (c.moves loc) hi)

/-- Computes the last page by the application `page S sc z loc c (Cfg).waves le_rfl`. -/
abbrev lastPage (c : Journal V k (Cfg).waves f) := page S sc z loc c (Cfg).waves le_rfl

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
end

/- # A polynomial bound on the selector width -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local

open scoped Classical in
theorem selectorBits_le_polynomial {A D M T Q c : ℕ} (hQ : Q ≤ (T + 1) ^ c) :
    selectorBits A D M T Q ≤ (A + 2 * (c + 1)) * (1 + Nat.clog 2 (T + 1)) * ((D ^ 5 + 1) * (M + 1))
      := by
  let t := Nat.clog 2 (T + 1)
  have hd : T + 1 ≤ 2 ^ t := Nat.le_pow_clog (by decide) _
  have hl : Nat.clog 2 (Q + 1) ≤ t * c + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ' 2 (t * c), pow_mul 2 t c]
    have hOne : 1 ≤ (T + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
    refine (Nat.add_le_add hQ hOne).trans ?_
    rw [← two_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _)
  have hb : t * c + 1 ≤ (c + 1) * (1 + t) := by
    rw [add_mul, mul_add, one_mul, mul_one, mul_comm c t]
    omega
  unfold selectorBits
  apply Nat.mul_le_mul_right
  change A * (1 + t) + Nat.clog 2 (Q + 1) * 2 ≤ (A + 2 * (c + 1)) * (1 + t)
  rw [add_mul]
  apply Nat.add_le_add_left
  exact (Nat.mul_le_mul_right 2 (hl.trans hb)).trans_eq (by ring)

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
end

/- # Transferring concentration back to the original seating -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input

open Coloring Packing Assembly Transcript

namespace Seating
variable {F : Type} [Field F] {x y : Wire} {h D T R g a e m : ℕ} {W : ℝ}
    {P : Input F x y h D T R g W} {read : BundleReader F a e}
    (v : P.Seating m) (o : BundleOrder P.diagram read)

open scoped Classical in
theorem return_concentrated {u C d ℓ : ℕ} {Z : LocalTerm F x y h u}
    (hz : Concentrated (v.ordered o) Z C d ℓ) : Concentrated P Z C d ℓ :=
  ⟨hz.cells, hz.coreDegree, hz.fullDegree, hz.frozenCount, hz.frozenMax, hz.frozenSquare,
    hz.coreMax, hz.coreSum⟩

end Seating
end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
end
