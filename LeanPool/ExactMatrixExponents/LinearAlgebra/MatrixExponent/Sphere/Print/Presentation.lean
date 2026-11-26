/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Traces
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Print.Pins
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Order.History

/-! # A directed, unit-width presentation of the full ordered diagram -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Frame
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout Coloring Assembly

variable {F α A : Type} [Field F] {a b : Wire} {u : ℕ} {G : Bundled F a b}
  {U : Engine F A} {r : U.scheme.format.obj} {N : Names G A U.d} {p : Order.Script G α}
  (H : Frame U r N p u)

open Classical in
/-- Builds `Seating U.scheme r p.drawing.diagram where vertex` with the specified `vertex`,
`ends`, `station`, `value`. -/
def seating : Seating U.scheme r p.drawing.diagram where
  vertex := H.vertex
  ends := H.ends
  station := H.owner
  value := H.value
  empty v hv t := by
    have he (q : Pattern F U.d 0 U.e) (h : q = Star.vacant)
        (x : ∀ s, Fin (q.width v.2.2 s) → Bool) : q.value v.2.2 x = 1 := by subst q; rfl
    exact he _ (H.inactive v hv) _

open Classical in
/-- Builds `U.scheme.Presentation r p.drawing.diagram where toSeating` with the specified
`toSeating`, `proper`, `internal`, `rw`. -/
def presentation : U.scheme.Presentation r p.drawing.diagram where
  toSeating := H.seating.seat
  proper := H.proper
  internal e := by
    rw [H.seating.ends_eq]
    change U.scheme.Joins r (H.ends (.inl (.inr e))) (H.ends (.inr (.inr e)))
    rw [H.lbit, H.rbit]
    exact ⟨(H.unit_info false e.1 _ (H.unit_lt _ e.2)).2.2, rfl⟩
  input i := by
    obtain ⟨⟨v, j⟩, rfl⟩ := p.left.enum.full.surjective i
    rw [H.seating.ends_eq]
    change U.scheme.peer r (H.ends (.inl (.inl (p.left.enum.get v j)))).1 = none
    rw [H.left v j]
    exact (H.exterior_info v false).2.2
  output i := by
    obtain ⟨⟨v, j⟩, rfl⟩ := p.right.enum.full.surjective i
    rw [H.seating.ends_eq]
    change U.scheme.peer r (H.ends (.inr (.inl (p.right.enum.get v j)))).1 = none
    rw [H.right v j]
    exact (H.exterior_info v true).2.2

open Classical in
theorem vertex_eq : H.presentation.vertex = H.vertex := rfl

open Classical in
theorem ends_eq : H.presentation.toSeating.ends = H.ends := H.seating.ends_eq

open Classical in
theorem directed : H.presentation.Directed := by
  intro q
  rw [H.ends_eq]
  exact H.directed_end q

include H in
open Classical in
theorem uniform (i : U.scheme.Span) (hi : (U.scheme.peer r i).isSome) : U.scheme.width r i = u := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hi
  obtain ⟨s, e, t, ht, rfl, _⟩ := H.peer_spec _ _ hj
  exact (H.unit_info s e t ht).1

open Classical in
theorem neighbor (v w : G.V) (i j : B U.e)
    (h : U.scheme.peer r (H.vertex v, i) = some (H.vertex w, j)) :
    (U.scheme.pattern r (H.vertex v)).peer 0 i = some (N.near v w, 0, j) := by
  obtain ⟨s, e, l, hl, hi, hj⟩ := H.peer_spec _ _ h
  obtain ⟨hv, rfl⟩ := Prod.mk.inj hi
  obtain ⟨hw, rfl⟩ := Prod.mk.inj hj
  rw [H.vertex.injective hv, H.vertex.injective hw]
  exact H.unit_local s e l hl

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Frame
end

/- # A local printer for all the physical descendants of a station -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout Coloring

open Classical in
/-- The data for the inventory construction, including `ext`, `lines`, `command`. -/
structure Inventory (F α A X : Type) where
  /-- The `Inventory` component of type `Bool → ℕ`. -/
  ext : Bool → ℕ
  /-- The `Inventory` component of type `Set (Arc α A X)`. -/
  lines : Set (Arc α A X)
  /-- The `Inventory` component of type `Policy F α A`. -/
  command : Policy F α A

variable {F X A α I V : Type} [Field F] {a b : Wire} {d z : ℕ} {G : Bundled F a b}
  {T : Trie V d}

open Classical in
/-- Uses `⟨Names.extSize p v, cloud p lane name v, policy p lane v⟩` as the representation. -/
def describe (p : Order.Script G α) (lane : G.E → A) (name : G.V → X) (v : G.V) :
    Inventory F α A X := ⟨Names.extSize p v, cloud p lane name v, policy p lane v⟩

open Classical in
/-- The value specified by `printStar x (channels x w u c.lines) near (if x.isLeft then c.ext
else fun _ => 0) (routePolicy x w c.lines c.command)`. -/
def Inventory.star (c : Inventory F α A X) (x : Node X d) (u : ℕ) (w : Branch X d)
    (near : Node X d → Node X d → B z) : Star F (Layer A d) z :=
  printStar x (channels x w u c.lines) near (if x.isLeft then c.ext else fun _ => 0)
    (routePolicy x w c.lines c.command)

variable (H : Fanout G T I) (u : ℕ) (lane : G.E → A) (hu : Unique G lane)
  (idx : Node G.V d → Node G.V d → B z)

open Classical in
/-- Computes the route names by the application `Unique.names (layer H u lane) (unique_layer H u
lane hu) idx`. -/
abbrev routeNames : Names (H.pad u).route.net (Layer A d) z
    := Unique.names (layer H u lane) (unique_layer H u lane hu) idx

open Classical in
/-- The inventory, branch assignments on its endpoints and neighbor
indices suffice for the whole star on any of the station's host slots. -/
theorem printed (p : Order.Script G α) (name : G.V → X) (v : Node G.V d)
    (hs : Same name (root v)) (w : Branch X d)
    (hf : ∀ e, touches G (root v) e → Follows H name w e)
    (near : Node X d → Node X d → B z)
    (hn : ∀ b e, side (H.pad u).route.net b e = v →
      near (lift name v) (lift name (side (H.pad u).route.net (!b) e)) =
        idx v (side (H.pad u).route.net (!b) e)) :
    (routeNames H u lane hu idx).star ((p.pad u).route (H.pad u).route) v =
      (describe p lane name (root v)).star (lift name v) u w near := by
  let N := routeNames H u lane hu idx
  let q := (p.pad u).route (H.pad u).route
  have h : Names.extSize q v = if (lift name v).isLeft then Names.extSize p (root v) else fun _
    => 0 := by
    cases v <;> funext s <;> cases s <;> rfl
  calc
    _ = printStar (lift name v) (cloud q (layer H u lane) (lift name) v) near
        (Names.extSize q v) (policy q (layer H u lane) v) := by
      apply star_eq N q v (lift name) (unique_layer H u lane hu) (same_layer H u name v hs)
      intro b e he
      change _ = idx (side _ b e) (side _ (!b) e)
      rw [he]
      exact hn b e he
    _ = _ := by
      rw [h]
      unfold q
      rw [routed_cloud H u lane p name w v hs hf, policy_routed H u lane p name w hu v hs hf]
      rfl

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
end

/-
# Static local navigation

A guide remembers no long host names. It stores the short branch
addresses and neighbor indices between the possible slots of a cell
and its neighbors. These functions are shared across all blocks.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout Coloring

variable {F V X Y I α A : Type} {d z : ℕ}

open Classical in
/-- The data for the guide construction, including `branch`, `next`. -/
structure Guide (X : Type) (d z : ℕ) where
  /-- The `Guide` component of type `Branch X d`. -/
  branch : Branch X d
  /-- The successor of each choice of type `Node X d → Node X d → B z`. -/
  next : Node X d → Node X d → B z

open Classical in
/-- Builds `Guide X d z where branch x y` with the specified `Guide`, `next`. -/
def Guide.make (T : Trie V d) (index : Node V d → Node V d → B z) (find : X → V) :
    Guide X d z where
  branch x y := T.address (find x) (find y)
  next x y := index (lift find x) (lift find y)

open Classical in
/-- Transforms the indexed data by `p.map (fun s => s.star v u W.branch W.next)`. -/
def Guide.emit [Field F] (W : Guide X d z) (v : Node X d) (u : ℕ)
    (p : Option (Inventory F α A X)) : Option (Star F (Layer A d) z) :=
  p.map (fun s => s.star v u W.branch W.next)

variable {a b : Wire} {G : Bundled F a b} {T : Trie V d} (H : Fanout G T I)
  (idx : Node V d → Node V d → B z)

open Classical in
/-- Computes the pointer by the application `idx (H.place v).1 (H.place w).1`. -/
def pointer (v w : Node G.V d) := idx (H.place v).1 (H.place w).1

open Classical in
/-- The condition `∀ w, (w = v ∨ ∃ e, touches G v e ∧ touches G w e) → find (name w) = (H.site
w).1` on the specified data. -/
def Locates (name : G.V → X) (find : X → V) (v : G.V) :=
  ∀ w, (w = v ∨ ∃ e, touches G v e ∧ touches G w e) → find (name w) = (H.site w).1

open Classical in
private theorem lift_name (name : G.V → X) (find : X → V) (v : Node G.V d)
    (h : find (name (root v)) = (H.site (root v)).1) :
    lift find (lift name v) = (H.place v).1 := by
  cases v with
  | inl v => exact congrArg Sum.inl h
  | inr v => exact congrArg (fun x => Sum.inr (x, v.2)) h

variable [Field F]

open Classical in
theorem print_local (u : ℕ) (lane : G.E → A) (hu : Unique G lane) (p : Order.Script G α)
    (name : G.V → X) (v : Node G.V d) (hs : Same name (root v))
    (find : X → V) (hf : Locates H name find (root v)) :
    (Guide.make T idx find).emit (lift name v) u (some (describe p lane name (root v))) =
      some ((routeNames H u lane hu (pointer H idx)).star ((p.pad u).route (H.pad u).route) v) := by
  let W := Guide.make T idx find
  have follows (e : G.E) (he : touches G (root v) e) : Follows H name W.branch e := by
    intro s
    change T.address (find (name _)) (find (name _)) = _
    have ht (s : Bool) := hf _ (.inr ⟨e, he, touches_side _ s e⟩)
    rw [ht, ht]
  have step b i (h : side (H.pad u).route.net b i = v) :
      W.next (lift name v) (lift name (side (H.pad u).route.net (!b) i)) =
        pointer H idx v (side (H.pad u).route.net (!b) i) := by
    let w := side (H.pad u).route.net (!b) i
    have hv : touches G (root v) i.1 := h ▸ end_root H u b i
    change idx (lift find (lift name v)) (lift find (lift name w)) = _
    rw [lift_name H name find v (hf _ (.inl rfl)),
      lift_name H name find w (hf _ (.inr ⟨i.1, hv, end_root H u (!b) i⟩))]
    rfl
  exact congrArg some (printed H u lane hu (pointer H idx) p name v hs W.branch follows W.next
    step).symm

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
end

/- Local programs, including the order of all station and sphere operands. -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Order

variable {F U X E V K J Z A : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y}

open Classical in
/-- Returns `some h.choose` when `h : ∃ i ∈ c.rows, i.number = z` holds, and `none` otherwise. -/
def Sheet.get (c : Sheet F J Z A M r t) (z : Z) :=
  if h : ∃ i ∈ c.rows, i.number = z then some h.choose else none

open Classical in
theorem Sheet.get_spec (c : Sheet F J Z A M r t) {z : Z} {i} (h : c.get z = some i) :
    i ∈ c.rows ∧ i.number = z := by
  unfold get at h
  split_ifs at h with he
  exact Option.some.inj h ▸ he.choose_spec

open Classical in
/-- The indexed operation `i.reads.map (fun k => .reader k v i.number) ++ List.ofFn (Lane.left v
i.number) ++ List.ofFn (Lane.right v i.number)`. -/
def Row.operands (i : Row F Z A M r t) (v : J) : List (Lane J Z A M) :=
  i.reads.map (fun k => .reader k v i.number) ++ List.ofFn (Lane.left v i.number) ++
    List.ofFn (Lane.right v i.number)

namespace Sheet
variable [Field F] (c : Sheet F J Z A M r t) (P : ℕ)

open Classical in
/-- The first of type `Policy F (Signal M r t) (Lane J Z A M)` for the given inputs. -/
def first (j : Fin M) : Policy F (Signal M r t) (Lane J Z A M) :=
  operation (chamber Signal.first
    (c.rows.map (fun i => i.point ^ P) ++ c.ports.map (fun i => i.point ^ P)))
    (c.rows.map (fun i => Lane.left c.mark i.number j) ++ c.ports.map (fun i => Lane.seam i.edge j))

open Classical in
/-- The indexed operation `operation (chamber Signal.second (c.rows.map Row.point)) (c.rows.map
(fun i => Lane.right c.mark i.number j))`. -/
def second (j : Fin M) : Policy F (Signal M r t) (Lane J Z A M) :=
  operation (chamber Signal.second (c.rows.map Row.point))
    (c.rows.map (fun i => Lane.right c.mark i.number j))

open Classical in
/-- The job of type `Option ((Bool → ℕ) × Policy F (Signal M r t) (Lane J Z A M))` for the given
inputs. -/
def job (known : J → A → Prop) (z : Spot J Z M) :
    Option ((Bool → ℕ) × Policy F (Signal M r t) (Lane J Z A M)) :=
  match z.2 with
  | .inl i => (c.get i).map (fun j => (j.ext, operation (load j.label) (j.operands c.mark)))
  | .inr (.inl false) => some (fun _ => 0, tests (c.hub known))
  | .inr (.inl true) => some (fun _ => 0, operation (fun _ _ _ => 1) [])
  | .inr (.inr (.inl j)) => some (fun _ => 0, c.first P j)
  | .inr (.inr (.inr j)) => some (fun _ => 0, c.second j)

open Classical in
/-- Returns `(c.job P known z).map (fun x => ⟨x.1, c.lines known z, x.2⟩)` when `z.1 = c.mark`
holds, and `none` otherwise. -/
def inventory (known : J → A → Prop) (z : Spot J Z M) :
    Option (Inventory F (Signal M r t) (Lane J Z A M) (Spot J Z M)) :=
  if z.1 = c.mark then (c.job P known z).map (fun x => ⟨x.1, c.lines known z, x.2⟩) else none

end Sheet

namespace Marking
variable (m : Marking S J Z A) (L : Rules S) {e : E → ℕ} (p : Profile C e)

open Classical in
theorem get_eq (i : Place C) :
    (m.sheet L p i.1).get (m.number i) = some (m.rowData L p i) := by
  have h : ∃ j ∈ (m.sheet L p i.1).rows, j.number = m.number i :=
    ⟨_, m.row_mem L p i, rfl⟩
  rw [Sheet.get, dite_eq_left h]
  obtain ⟨j, hj, he⟩ := m.row_spec L p h.choose_spec.1
  have hn := h.choose_spec.2
  rw [← he] at hn ⊢
  rw [m.atCell j i hj hn]

variable [Field F] [Fintype E] [Fintype V] [Fintype K] (P : ℕ)

omit [Field F] in
open Classical in
private theorem row_operands (i : Place C) :
    (L.operands (.inl (.inl i))).map m.lane = (m.rowData L p i).operands (m.mark i.1) := by
  simp only [Rules.operands, Row.operands, rowData, List.map_append, List.map_map, List.map_ofFn]
  congr 2
  rw [← List.attach_map_val (l := L.reads i)]
  rfl

open Classical in
theorem first_eq (v : V) (j : Fin M) :
    policy (L.script p P) m.lane (.inr (.inl (v, j))) = (m.sheet L p v).first P j := by
  change operation (chamber Signal.first ((firstList C v).map (firstPoint C P)))
    (((firstList C v).map (Rules.first j)).map m.lane) = _
  unfold Sheet.first sheet
  simp only [firstList, secondList, List.map_append, List.map_map]
  rfl

open Classical in
theorem second_eq (v : V) (j : Fin M) :
    policy (L.script p P) m.lane (.inr (.inr (v, j))) = (m.sheet L p v).second j := by
  change operation (chamber Signal.second ((secondList C v).map (secondPoint C)))
    (((secondList C v).map (fun i => Rules.back i j)).map m.lane) = _
  unfold Sheet.second sheet
  simp only [secondList, List.map_map]
  rfl

open Classical in
private theorem job_eq (known : J → A → Prop) (s : S.Position) (h : m.Observes (S.home s) known) :
    (m.sheet L p (S.home s)).job P known (m.spot s) =
      some (Names.extSize (L.script p P) s, policy (L.script p P) m.lane s) := by
  rcases s with ((i|v|v)|(⟨v, j⟩|⟨v, j⟩))
  · change ((m.sheet L p i.1).get (m.number i)).map _ = _
    rw [m.get_eq, Option.map_some]
    change some ((m.rowData L p i).ext, operation (load (L.label i))
      ((m.rowData L p i).operands (m.mark i.1))) = _
    rw [← m.row_operands]
    rfl
  · rw [m.hub_eq L p v known h]
    refine congrArg some (Prod.ext ?_ rfl)
    funext b; cases b <;> rfl
  · refine congrArg some (Prod.ext ?_ rfl)
    funext b; cases b <;> rfl
  · rw [m.first_eq]
    refine congrArg some (Prod.ext ?_ rfl)
    funext b; cases b <;> rfl
  · rw [m.second_eq]
    refine congrArg some (Prod.ext ?_ rfl)
    funext b; cases b <;> rfl

open Classical in
theorem inventory_eq (known : J → A → Prop) (s : S.Position) (h : m.Observes (S.home s) known) :
    (m.sheet L p (S.home s)).inventory P known (m.spot s) =
      some (describe (L.script p P) m.lane m.spot s) := by
  have he : (m.spot s).1 = (m.sheet L p (S.home s)).mark := m.home_mark s
  rw [Sheet.inventory, ite_eq_left he, m.job_eq L p P known s h, Option.map_some]
  rw [m.lines L p known P s h]
  rfl

omit [Fintype E] [Fintype V] [Fintype K] in
open Classical in
theorem inventory_live (known : J → A → Prop) (v : V) (s : Spot J Z M)
    (h : ((m.sheet L p v).inventory P known s).isSome) :
    ∃ z, S.home z = v ∧ m.spot z = s := by
  unfold Sheet.inventory at h
  split_ifs at h with he
  swap
  · contradiction
  obtain ⟨j, i | (_ | _) | i | i⟩ := s
  all_goals change j = m.mark v at he
  all_goals subst j
  · change ((m.sheet L p v).get i |>.map _ |>.map _).isSome at h
    obtain ⟨u, hu⟩ : ∃ u, (m.sheet L p v).get i = some u := by
      cases eq : (m.sheet L p v).get i
      · simp [eq] at h
      · exact ⟨_, rfl⟩
    obtain ⟨hm, hn⟩ := (m.sheet L p v).get_spec hu
    obtain ⟨z, hz, rfl⟩ := m.row_spec L p hm
    exact ⟨.inl (.inl z), hz, Prod.ext (congrArg m.mark hz) (congrArg Sum.inl hn)⟩
  · exact ⟨.inl (.inr (.inl v)), rfl, rfl⟩
  · exact ⟨.inl (.inr (.inr v)), rfl, rfl⟩
  · exact ⟨.inr (.inl (v, i)), rfl, rfl⟩
  · exact ⟨.inr (.inr (v, i)), rfl, rfl⟩

end Marking
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
end

/-
# Local requests for printed patterns

A cell has one sheet for all its descendants. Footprints of neighbor
cells are addressed by color rather than by absolute position.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout Coloring Assembly

open Classical in
/-- The data for the request construction, including `sheet`, `footprint`, `guide`, `seat`. -/
structure Request (F J Z A : Type) (M r t d z : ℕ) where
  /-- The `Request` component of type `Sheet F J Z A M r t`. -/
  sheet : Sheet F J Z A M r t
  /-- The `Request` component of type `Finset (J × A)`. -/
  footprint : Finset (J × A)
  /-- The `Request` component of type `Guide (Spot J Z M) d z`. -/
  guide : Guide (Spot J Z M) d z
  /-- The `Request` component of type `Node (Spot J Z M) d`. -/
  seat : Node (Spot J Z M) d

variable {F J Z A : Type} [Field F] {M r t d z c s : ℕ}

open Classical in
/-- The value specified by `(v, k) ∈ q.footprint`. -/
def Request.known (q : Request F J Z A M r t d z) (v : J) (k : A) := (v, k) ∈ q.footprint

open Classical in
/-- The value specified by `q.guide.emit q.seat u (q.sheet.inventory P q.known (root q.seat))`. -/
def Request.emit (q : Request F J Z A M r t d z) (P u : ℕ) :=
  q.guide.emit q.seat u (q.sheet.inventory P q.known (root q.seat))

open Classical in
/-- Transforms the indexed data by `((x.bind fun q => q.emit P u).map fun b => b.pattern ix
u).getD Star.vacant`. -/
def pattern (x : Option (Request F J Z A M r t d z)) (P u : ℕ)
    (ix : Band (Layer (Lane J Z A M) d) c ↪ B s) :=
  ((x.bind fun q => q.emit P u).map fun b => b.pattern ix u).getD Star.vacant

open Classical in
theorem root_lift {V X : Type} (f : V → X) (v : Node V d) : root (lift f v) = f (root v) := by
  cases v <;> rfl

namespace Marking
variable {U X E V K : Type} [Fintype E] [Fintype V] [Fintype K]
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} (m : Marking S J Z A) (L : Order.Rules S) {e : E → ℕ} (p : Profile C e)
  (P u : ℕ) {I V' : Type} {T : Trie V' d} (H : Fanout (S.backdrop.emitted p P) T I)
  (idx : Node V' d → Node V' d → B z)

open Classical in
/-- Computes the names by the application `routeNames H u m.lane (m.unique p P) (pointer H
idx)`. -/
abbrev names := routeNames H u m.lane (m.unique p P) (pointer H idx)

open Classical in
theorem emit_eq (v : Node S.Position d) (x : Request F J Z A M r t d z)
    (h : x.sheet = m.sheet L p (S.home (root v)))
    (hobs : m.Observes (S.home (root v)) x.known) (hseat : x.seat = lift m.spot v)
    (find : Spot J Z M → V') (hloc : Locates H m.spot find (root v))
    (hg : x.guide = Guide.make T idx find) :
    x.emit P u = some ((m.names p P u H idx).star (((L.script p P).pad u).route (H.pad u).route) v)
      := by
  rw [Request.emit, hseat, hg, h, root_lift, m.inventory_eq L p P _ _ hobs]
  exact print_local H idx u m.lane (m.unique p P) (L.script p P) m.spot v (m.same p P _) find hloc

omit [Fintype E] [Fintype V] [Fintype K] in
open Classical in
theorem emit_live (v : V) (x : Request F J Z A M r t d z) (h : x.sheet = m.sheet L p v)
    (hx : (x.emit P u).isSome) :
    ∃ w : Node S.Position d, S.home (root w) = v ∧ lift m.spot w = x.seat := by
  have hr : ((m.sheet L p v).inventory P x.known (root x.seat)).isSome := by
    simpa [Request.emit, Guide.emit, h] using hx
  obtain ⟨w, hw, he⟩ := m.inventory_live L p P _ _ _ hr
  cases eq : x.seat with
  | inl s =>
    rw [eq] at he
    exact ⟨.inl w, hw, congrArg Sum.inl he⟩
  | inr s =>
    rw [eq] at he
    exact ⟨.inr (w, s.2), hw, congrArg (fun t => Sum.inr (t, s.2)) he⟩

end Marking
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
end

/- # Static host information for one colored cell -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
open Coloring Rounds
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout (Sharing Place Profile Alphabet
    Node)

open Classical in
/-- Indexes the number by the coordinates of `Bool × Fin (D ^ k)`. -/
abbrev Number (D k : ℕ) := Bool × Fin (D ^ k)
open Classical in
/-- Indexes the bench by the coordinates of `V × Sharing.Slot M D k`. -/
abbrev Bench (V : Type) (M D k : ℕ) := V × Sharing.Slot M D k
open Classical in
/-- The quantity computed by `Node (Bench V M D k) (Sharing.radius k * d)`. -/
abbrev Host (V : Type) (M D k d : ℕ) := Node (Bench V M D k) (Sharing.radius k * d)

namespace Compass

variable {F U X E V K : Type} {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k d : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  {G : S.Geo P k} (hD : D = 2 ^ d) (hd : 4 ≤ D)
  [Field F] [Fintype E] [Fintype V] [Fintype K]
  {e : E → ℕ} (p : Profile C e) (L : ℕ)

open Classical in
theorem home_eq (v : Node S.Position (Sharing.radius k * d)) :
    ((root ((G.layout hD hd p L).place v).1).1, ((G.layout hD hd p L).place v).2) =
      G.site (S.home (root v)) := by cases v <;> rfl

end Compass
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
end

/- # Active and vacant slots in a local emission -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
open Rounds
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout (Sharing Place Profile Alphabet
    Node)

open Classical in
/-- Indexes the page by the coordinates of `Sheet F J Z A M r t × Finset (J × A)`. -/
abbrev Page (F J Z A : Type) (M r t : ℕ) := Sheet F J Z A M r t × Finset (J × A)

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
end

/- # Building a directed presentation from printed occurrence rows -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
open Rounds Coloring
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout (Sharing Place Profile Alphabet
    Node)

open Classical in
/-- Embeds `V × I` into `U.scheme.Vtx`. -/
def Engine.seat {F A V I : Type} (U : Engine F A) (host : V ↪ B U.m) (block : I ↪ B U.h) :
    V × I ↪ U.scheme.Vtx :=
  ⟨fun x => (host x.1, block x.2, 0), fun _ _ h =>
    Prod.ext (host.injective (congrArg Prod.fst h)) (block.injective (congrArg (fun y => y.2.1) h))⟩

namespace Compass
variable {F T X E V K J A : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) T E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D W₀ R g k d : ℕ} {W : ℝ} {P : Input F a b h D W₀ R g W}
  {G : S.Geo P k}
  (hD : D = 2 ^ d) (hd : 4 ≤ D) {e : E → ℕ} (p : Profile C e) (L u : ℕ) (q : Order.Rules S)

open Classical in
/-- The quantity computed by `Layer (Lane J (Number D k) A M) (Sharing.radius k * d)`. -/
abbrev FinalLane (J A : Type) (M D k d : ℕ) := Layer (Lane J (Number D k) A M) (Sharing.radius k *
    d)

variable {U : Engine F (FinalLane J A M D k d)}
  (host : Host P.V M D k d ↪ B U.m) (block : Packing.Cell h ↪ B U.h)
  (idx : Host P.V M D k d → Host P.V M D k d → B U.d)
  (rows : U.scheme.format.obj)
  (pages : P.V × Packing.Cell h → Option (Page F J (Number D k) A M r t))

local notation "H" => G.layout hD hd p L

open Classical in
/-- Embeds `Node S.Position (Sharing.radius k * d)` into `U.scheme.Vtx`. -/
def vertex : Node S.Position (Sharing.radius k * d) ↪ U.scheme.Vtx :=
  (show Node S.Position (Sharing.radius k * d) ↪ _ from ⟨(H).place, (H).injective⟩).trans
    (U.seat host block)

end Compass
end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print
end
