(* The typed interface of each language satisfies the signature of the bool and
   num modules, though l2 has one more module (neg), so that host code written
   once over that signature runs on both. *)

module _ (L : L1_typed.S) : Num_sig.S = L
module _ (L : L2_typed.S) : Num_sig.S = L

module Host (L : Num_sig.S) = struct
  let num n = L.Num.mk_num (Z.of_int n)
  let three = L.Num.add (num 1) (num 2)

  let () =
    assert (L.Num.as_num three = Some (Z.of_int 3));
    assert (L.equal (L.Num.less (num 0) three) L.Bool.v_true);
    assert (L.Bool.is_tbool (L.type_of (L.Num.less three three)))
end

module _ = Host (L1_typed.Derived)
module _ = Host (L2_typed.Derived)
