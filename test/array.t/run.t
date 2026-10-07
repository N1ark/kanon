The immutable arrays, `t array`: a literal, `array_length`, `array_get`,
`array_set` (a copy), `array_of_list` and `array_to_list`, and structural
equality.

  $ cat > lang.knl <<'KN'
  > [@@@ocaml_prims "Prims"]
  > use "rules"
  > node Int of int : TInt
  > notation Int
  > node Vec of int array : TVec
  > sort TInt
  > sort TVec
  > KN
  $ cat > rules.kn <<'KN'
  > fn swap (a : int array) (i j : int) : int array =
  >   array_set (array_set a i (array_get a j)) j (array_get a i)
  > fn of_list (l : int list) : int array = array_of_list l
  > fn to_list (a : int array) : int list = array_to_list a
  > fn size (a : (int * bool) array array) : int = array_length a
  > fn lit (x : int) : int array = [| x; x + 1 |]
  > fn empty (a : int array) : int array = if array_length a = 0 then [||] else a
  > fn same (a b : int array) : bool = a = b && not (a <> b)
  > KN

OCaml: the standard `Iarray`, with nothing else than the generated code.

  $ kanon ocaml lang.knl | sed -n '/let\[@inline\] rules_swap/,$p'
    let[@inline] rules_swap (a : (Z.t Iarray.t)) (i : Z.t) (j : Z.t) : (Z.t Iarray.t) =
        (let a = (let a = a and i = Z.to_int i and v = (Stdlib.Iarray.get a (Z.to_int j)) in
                 let c = Stdlib.Iarray.to_array a in
                 c.(i) <- v;
                 Stdlib.Iarray.of_array c) and i = Z.to_int j and v = (Stdlib.Iarray.get a (Z.to_int i)) in
        let c = Stdlib.Iarray.to_array a in
        c.(i) <- v;
        Stdlib.Iarray.of_array c)
    
    let[@inline] rules_of_list (l : (Z.t list)) : (Z.t Iarray.t) =
        (Stdlib.Iarray.of_list l)
    
    let[@inline] rules_to_list (a : (Z.t Iarray.t)) : (Z.t list) =
        (Stdlib.Iarray.to_list a)
    
    let[@inline] rules_size (a : (((Z.t * bool) Iarray.t) Iarray.t)) : Z.t =
        (Z.of_int (Stdlib.Iarray.length a))
    
    let[@inline] rules_lit (x : Z.t) : (Z.t Iarray.t) =
        ([|x; (Z.add x Z.one)|] : _ Iarray.t)
    
    let[@inline] rules_empty (a : (Z.t Iarray.t)) : (Z.t Iarray.t) =
        (if ((Z.equal (Z.of_int (Stdlib.Iarray.length a)) Z.zero))
        then ([||] : _ Iarray.t)
        else a)
    
    let[@inline] rules_same (a : (Z.t Iarray.t)) (b : (Z.t Iarray.t)) : bool =
        ((((Stdlib.Iarray.equal Z.equal) a b)) && (not (not ((Stdlib.Iarray.equal Z.equal) a b))))
  end
  
  (** The Kanon module lang. *)
  module Lang = struct
    let t_int : ty = TInt
    let t_vec : ty = TVec
    
    let as_int (t : t) =
      match[@warning "-11"] t with { kind = Int (p1); _ } -> Some p1 | _ -> None
    
    let is_int (t : t) =
      match[@warning "-11"] t with { kind = Int (_); _ } -> true | _ -> false
    
    let as_vec (t : t) =
      match[@warning "-11"] t with { kind = Vec (p1); _ } -> Some p1 | _ -> None
    
    let is_vec (t : t) =
      match[@warning "-11"] t with { kind = Vec (_); _ } -> true | _ -> false
    
    let as_tint (t : ty) =
      match[@warning "-11"] t with TInt -> Some () | _ -> None
    
    let is_tint (t : ty) =
      match[@warning "-11"] t with TInt -> true | _ -> false
    
    let as_tvec (t : ty) =
      match[@warning "-11"] t with TVec -> Some () | _ -> None
    
    let is_tvec (t : ty) =
      match[@warning "-11"] t with TVec -> true | _ -> false
  end
  
  (** The Kanon module rules. *)
  module Rules = struct
    let swap = Kanon_flat.rules_swap
    let of_list = Kanon_flat.rules_of_list
    let to_list = Kanon_flat.rules_to_list
    let size = Kanon_flat.rules_size
    let lit = Kanon_flat.rules_lit
    let empty = Kanon_flat.rules_empty
    let same = Kanon_flat.rules_same
  end
  
  

The typed interface has the array type, and the destructor of a node that holds
one:

  $ sed 's|^\[@@@ocaml_prims "Prims"\]|&\n[@@@ocaml_rules "Rules"]|' lang.knl > typed.knl
  $ kanon ocaml-typed typed.knl | grep -n 'Iarray'
  42:    val as_vec : _ t -> (Z.t Iarray.t) option

The types define the structural equality and hash of a node with an array
argument.

  $ kanon ocaml-types lang.knl | grep -n "Iarray"
  7:  | Vec of (Z.t Iarray.t)
  28:  | Vec a1, Vec b1 -> (Stdlib.Iarray.equal Z.equal) a1 b1
  36:        ((Stdlib.Iarray.fold_left (fun acc x -> hash_combine acc (Z.hash x)) 0) a1)

Lean: `Array`, with the operations of Kanon's library (`KanonCore.Array`).

  $ kanon lean-node lang.knl | grep Array
    | Vec (x1 : (Array Int))
  $ kanon lean-model lang.knl | sed -n '/^def Rules.swap/,/^$/p'
  def Rules.swap (a : (Array Int)) (i : Int) (j : Int) : (Array Int) :=
    (arraySet (arraySet a i (arrayGet a j)) j (arrayGet a i))
  

Arrays have no list syntax: no cons, no concatenation, no patterns. Their
elements have one type, and their operations are checked.

  $ check() { printf '%s\n' "$1" > rules.kn; kanon ocaml lang.knl > /dev/null; }
  $ check 'fn f (a : int array) : int = array_get a true'
  ./rules.kn:1:41: type mismatch: expected int, got bool
  [1]
  $ check 'fn f (a : int array) : int array = array_set a 0 true'
  ./rules.kn:1:49: type mismatch: expected int, got bool
  [1]
  $ check 'fn f (a : int list) : int = array_length a'
  ./rules.kn:1:41: type mismatch: expected an array, got int list
  [1]
  $ check 'fn f (a : int array) : bool = array_length [||] = 0'
  ./rules.kn:1:43: cannot infer the type of [||]
  [1]
  $ check 'fn f : int array = [| 1; true |]'
  ./rules.kn:1:25: type mismatch: expected int, got bool
  [1]
  $ check 'fn f (a : int array) : int = array_get a'
  ./rules.kn:1:29: array_get expects 2 arguments, got 1
  [1]
  $ check 'fn f (a : int array) : int = match a with [||] -> 0 | _ -> 1'
  ./rules.kn:1:42: syntax error
  [1]
  $ check 'fn f (a : int array) : int array = 1 :: a'
  ./rules.kn:1:40: type mismatch: expected int list, got int array
  [1]
  $ check 'fn array_get (a : int) : int = a'
  ./rules.kn:1:3: array_get is built in
  [1]
  $ check 'prim array_length : int -> int'
  ./rules.kn:1:5: array_length is built in
  [1]
  $ check 'fn f (a : int array) (b : bool array) : bool = a = b'
  ./rules.kn:1:51: type mismatch: expected int array, got bool array
  [1]
