The typing of a node, in Lang.lean of its module: its typing, and the
invariants of the node and of its sort ([@lean_inv "P"]), predicates that its
hand-written Sem.lean defines, over the same arguments as the typing: the sorts
of the modules in a language, the types of the children, the node and its sort.
The typing of the terms among its arguments is that of its children
(`Node.All`).

  $ kanon lean-all out lang.knl
  $ sed -n '/^def Node.wt/,/^$/p' out/CoreMod/Generated/Lang.lean
  def Node.wt {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sCore : (CoreMod.Srt Ty) → Ty) (ty : T → Ty) : (Node Ty) T → Ty → Prop
    | (.Ev x1), t => (t = (sCore .TEven)) ∧ even_inv sBool sCore ty (.Ev x1) t
    | (.Seq l1), t => seq_wt sBool sCore ty (.Seq l1) t
    | (.Exists x1 a2), t => (t = (sBool .TBool)) ∧ exists_wf sBool sCore ty (.Exists x1 a2) t
    | (.Arr x1 x2), t => True
  

A sort that takes sorts (TSeq of ty) is over the sorts of a language, and so is
a node that takes sorts among its arguments (the binders of Exists).

  $ grep -A1 '^inductive' out/CoreMod/Generated/Node.lean
  inductive Srt (Ty : Type) where
    | TEven
  --
  inductive Node (Ty : Type) (T : Type) where
    | Ev (x1 : Int)

Children may be inside other types (an array, an option, a tuple, a record):
the functions of each such type map its terms and list them, and the
relation of two nodes compares their shapes and the lists of their children.

  $ grep '^def _root_\|^  | (.Arr' out/CoreMod/Generated/Node.lean
  def _root_.CoreMod.Node.shape1.map {T U : Type} (f : T → U) : (List T) → (List U)
  def _root_.CoreMod.Node.shape1.flat {T : Type} : (List T) → List T
  def _root_.CoreMod.Node.shape2.map {T U : Type} (f : T → U) : (Array T) → (Array U)
  def _root_.CoreMod.Node.shape2.flat {T : Type} : (Array T) → List T
  def _root_.CoreMod.Node.shape3.map {T U : Type} (f : T → U) : (Int × T) → (Int × U)
  def _root_.CoreMod.Node.shape3.flat {T : Type} : (Int × T) → List T
  def _root_.CoreMod.Node.shape4.map {T U : Type} (f : T → U) : (Option (Int × T)) → (Option (Int × U))
  def _root_.CoreMod.Node.shape4.flat {T : Type} : (Option (Int × T)) → List T
    | (.Arr x1 x2) => (.Arr (CoreMod.Node.shape2.map f x1) (CoreMod.Node.shape4.map f x2))
    | (.Arr x1 x2) => (∀ y ∈ CoreMod.Node.shape2.flat x1, P y) ∧ (∀ y ∈ CoreMod.Node.shape4.flat x2, P y)
    | (.Arr x1 x2), (.Arr x1' x2') => CoreMod.Node.shape2.map (fun _ => ()) x1 = CoreMod.Node.shape2.map (fun _ => ()) x1' ∧ Kanon.Forall₂ R (CoreMod.Node.shape2.flat x1) (CoreMod.Node.shape2.flat x1') ∧ CoreMod.Node.shape4.map (fun _ => ()) x2 = CoreMod.Node.shape4.map (fun _ => ()) x2' ∧ Kanon.Forall₂ R (CoreMod.Node.shape4.flat x2) (CoreMod.Node.shape4.flat x2')
    | (.Arr x1 x2) => CoreMod.Node.shape2.flat x1 ++ CoreMod.Node.shape4.flat x2
