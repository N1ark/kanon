The typing law of a node, in the interface of its module: its typing, the
typing of the terms among its arguments, and the invariants of the node and of
its sort ([@lean_inv "P"]), which are fields of the interface.

  $ kanon lean-all out lang.knl
  $ grep -E '_inv|_wt|_wf|WT_' out/CoreMod/Syntax.lean
    seq_wt : S.Term → Prop
    exists_wf : S.Term → Prop
    even_inv : S.Term → Prop
    WT_Ev : ∀ (x1 : Int) (t : S.Ty), S.WT (B.node (EvK x1) t) ↔ t = TEven ∧ even_inv (B.node (EvK x1) t)
    WT_Seq : ∀ (x1 : (List S.Term)) (t : S.Ty), S.WT (B.node (SeqK x1) t) ↔ (∀ y ∈ x1, S.WT y) ∧ seq_wt (B.node (SeqK x1) t)
    WT_Exists : ∀ (x1 : (List Int)) (x2 : S.Term) (t : S.Ty), S.WT (B.node (ExistsK x1 x2) t) ↔ t = LBool.TBool ∧ S.WT x2 ∧ exists_wf (B.node (ExistsK x1 x2) t)
