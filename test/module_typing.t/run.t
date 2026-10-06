The typing of a node, in Lang.lean of its module: its typing, and the
invariants of the node and of its sort ([@lean_inv "P"]), predicates that its
hand-written Sem.lean defines, over the same arguments as the typing: the sorts
of the modules in a language, the types of the children, the node and its sort.
The typing of the terms among its arguments is that of its children
(`Node.All`).

  $ kanon lean-all out lang.knl
  $ sed -n '/^def Node.wt/,/^$/p' out/CoreMod/Lang.lean
  def Node.wt {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sCore : (CoreMod.Srt Ty) → Ty) (ty : T → Ty) : (Node Ty) T → Ty → Prop
    | (.Ev x1), t => (t = (sCore .TEven)) ∧ even_inv sBool sCore ty (.Ev x1) t
    | (.Seq l1), t => seq_wt sBool sCore ty (.Seq l1) t
    | (.Exists x1 a2), t => (t = (sBool .TBool)) ∧ exists_wf sBool sCore ty (.Exists x1 a2) t
  

A sort that takes sorts (TSeq of ty) is over the sorts of a language, and so is
a node that takes sorts among its arguments (the binders of Exists).

  $ grep -A1 '^inductive' out/CoreMod/Node.lean
  inductive Srt (Ty : Type) where
    | TEven
  --
  inductive Node (Ty : Type) (T : Type) where
    | Ev (x1 : Int)
