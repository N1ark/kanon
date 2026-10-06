The typing of a node, in Lang.lean of its module: its typing, and the
invariants of the node and of its sort ([@lean_inv "P"]), predicates over the
nodes of the module that its hand-written Sem.lean defines. The typing of the
terms among its arguments is that of its children (`Node.All`).

  $ kanon lean-all out lang.knl
  $ sed -n '/^def Node.wt/,/^$/p' out/CoreMod/Lang.lean
  def Node.wt {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sCore : CoreMod.Srt → Ty) (ty : T → Ty) : Node T → Ty → Prop
    | (.Ev x1), t => (t = (sCore .TEven)) ∧ even_inv (T := T) (.Ev x1)
    | (.Seq l1), t => seq_wt (T := T) (.Seq l1)
    | (.Exists x1 a2), t => (t = (sBool .TBool)) ∧ exists_wf (T := T) (.Exists x1 a2)
  
