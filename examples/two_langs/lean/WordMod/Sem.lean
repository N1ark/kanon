import WordMod.Generated.Node
import KanonBool.Sem

/-!
# The meaning of the nodes of the word module

Words are integers (`WordMod.Values`); the width of a word is in its sort
only. The invariant `word_wf` of blobs and fitted integers (part of their
typing) is that their integer fits their width.
-/

noncomputable section

namespace WordMod

open Classical Kanon
open Kanon.Sem (OLe)

/-- What the word module needs of the values of a language: its words. -/
class Values (D : Kanon.Dom) where
  vword : Embed Int D.Val

/-- The width of an integer, which the typing of `WFit` uses. -/
def fit (z : Int) : Int := z.natAbs.log2 + 1

/-- The invariant of blobs and fitted integers: their integer fits their
width. Like the typing of the nodes, it is given the sorts of the modules in
a language and the types of the children, which it does not use. -/
def word_wf {T Ty : Type} (sBool : KanonBool.Srt → Ty) (sWord : Srt → Ty) (ty : T → Ty) :
    Node T → Ty → Prop
  | .WBlob b _, _ => b.bits < 256
  | .WFit z, _ => 0 ≤ z
  | _, _ => True

/-- The sum of two words; poison otherwise. -/
def addV {D : Kanon.Dom} [Values D] (a b : Option D.Val) : Option D.Val :=
  a.bind fun x => b.bind fun y => (Values.vword.proj x).bind fun m =>
    (Values.vword.proj y).map fun n => Values.vword.inj (m + n)

@[kanon_val] theorem addV_eq_some {D : Kanon.Dom} [Values D] {a b : Option D.Val} {r : D.Val} :
    addV a b = some r ↔
      ∃ m n, a = some (Values.vword.inj m) ∧ b = some (Values.vword.inj n) ∧
        r = Values.vword.inj (m + n) := by
  constructor
  · intro h
    simp only [addV, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      Embed.proj_eq_some_iff] at h
    obtain ⟨_, rfl, _, rfl, m, rfl, n, rfl, rfl⟩ := h
    exact ⟨m, n, rfl, rfl, rfl⟩
  · rintro ⟨m, n, rfl, rfl, rfl⟩
    simp [addV]

/-- The evaluation of a node, given the values of its children in every
environment: rounding and widening keep the integer. -/
def Node.eval {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty) :
    Node (D.Env → Option D.Val) → Option D.Val
  | .Wd z _ => some (Values.vword.inj z)
  | .WBlob b _ => some (Values.vword.inj b.bits)
  | .WFit z => some (Values.vword.inj z)
  | .WAdd _ _ a b => addV (a ρ) (b ρ)
  | .WRound _ _ a => a ρ
  | .WExt _ a => a ρ

theorem Node.eval_mono {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (D.Env → Option D.Val)} (h : n.Rel Sem.FLe n') : OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  all_goals simp only [Node.eval]
  · obtain ⟨rfl, -⟩ := h; exact OLe.refl _
  · obtain ⟨rfl, -⟩ := h; exact OLe.refl _
  · subst h; exact OLe.refl _
  · intro v e
    rw [addV_eq_some] at e ⊢
    obtain ⟨m, k, h1, h2, rfl⟩ := e
    exact ⟨m, k, h.2.2.1 ρ _ h1, h.2.2.2 ρ _ h2, rfl⟩
  · exact h.2.2 ρ
  · exact h.2 ρ

/-- The values of the sorts of the module: words. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt → D.Val → Prop
  | .TWord _, v => ∃ z, v = Values.vword.inj z

end WordMod
