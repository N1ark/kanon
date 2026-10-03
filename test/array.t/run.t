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

  $ kanon ocaml lang.knl | sed -n '/let\[@inline\] swap/,$p'
  let[@inline] swap (a : (Z.t Iarray.t)) (i : Z.t) (j : Z.t) : (Z.t Iarray.t) =
      (let a = (let a = a and i = Z.to_int i and v = (Iarray.get a (Z.to_int j)) in
               let c = Iarray.to_array a in
               c.(i) <- v;
               Iarray.of_array c) and i = Z.to_int j and v = (Iarray.get a (Z.to_int i)) in
      let c = Iarray.to_array a in
      c.(i) <- v;
      Iarray.of_array c)
  
  let[@inline] of_list (l : (Z.t list)) : (Z.t Iarray.t) = (Iarray.of_list l)
  
  let[@inline] to_list (a : (Z.t Iarray.t)) : (Z.t list) = (Iarray.to_list a)
  
  let[@inline] size (a : (((Z.t * bool) Iarray.t) Iarray.t)) : Z.t =
      (Z.of_int (Iarray.length a))
  
  let[@inline] lit (x : Z.t) : (Z.t Iarray.t) =
      ([|x; (Z.add x Z.one)|] : _ Iarray.t)
  
  let[@inline] empty (a : (Z.t Iarray.t)) : (Z.t Iarray.t) =
      (if ((Z.equal (Z.of_int (Iarray.length a)) Z.zero))
      then ([||] : _ Iarray.t)
      else a)
  
  let[@inline] same (a : (Z.t Iarray.t)) (b : (Z.t Iarray.t)) : bool =
      ((((Iarray.equal Z.equal) a b)) && (not (not ((Iarray.equal Z.equal) a b))))
  
  

The types define the structural equality and hash of a node with an array
argument.

  $ kanon ocaml-types lang.knl | grep -n "Iarray"
  7:  | Vec of (Z.t Iarray.t)
  28:  | Vec a1, Vec b1 -> (Iarray.equal Z.equal) a1 b1
  36:        ((Iarray.fold_left (fun acc x -> hash_combine acc (Z.hash x)) 0) a1)

Lean: `Array`, with the operations of Kanon's library (`KanonCore.Array`).

  $ kanon lean-types lang.knl | grep Array
    | Vec : (Array Int) → Kind
  $ kanon lean-model lang.knl | sed -n '/^def swap/,/^\/-- The rule functions/p'
  def swap (a : (Array Int)) (i : Int) (j : Int) : (Array Int) :=
    (arraySet (arraySet a i (arrayGet a j)) j (arrayGet a i))
  
  def of_list (l : (List Int)) : (Array Int) :=
    (List.toArray l)
  
  def to_list (a : (Array Int)) : (List Int) :=
    (Array.toList a)
  
  def size (a : (Array (Array (Int × Bool)))) : Int :=
    (arrayLength a)
  
  def lit (x : Int) : (Array Int) :=
    #[x, (x + (1 : Int))]
  
  def empty (a : (Array Int)) : (Array Int) :=
    (if (decide ((arrayLength a) = (0 : Int))) then #[] else a)
  
  def same (a : (Array Int)) (b : (Array Int)) : Bool :=
    ((decide (a = b)) && (! (decide (a ≠ b))))
  
  /-- The rule functions, as used by the rules. -/

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
