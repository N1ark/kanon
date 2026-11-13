import KanonCore.Proof

/-! `kanon_cases` keeps the value of the atom that it splits, `ev ρ t = some v`,
for the closing lemmas that relate it to facts on the term `t`. -/

namespace KanonTest.CasesAtom

open Kanon

inductive Val where
  | int (z : Int)
  | bool (b : Bool)

def Val.asInt : Val → Option Int
  | .int z => some z
  | _ => none

def vint : Embed Int Val where
  inj := .int
  proj := Val.asInt
  proj_inj _ := rfl
  inj_proj b a h := by cases b <;> simp_all [Val.asInt]

/-- The remainder of an integer value by two. -/
def mod2V (o : Option Val) : Option Val := o.bind fun x => (vint.proj x).map fun z => vint.inj (z % 2)

theorem mod2V_eq_some {o : Option Val} {r : Val} :
    mod2V o = some r ↔ ∃ z, o = some (vint.inj z) ∧ r = vint.inj (z % 2) := by
  constructor
  · intro h
    simp only [mod2V, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      Embed.proj_eq_some_iff] at h
    obtain ⟨_, rfl, z, rfl, rfl⟩ := h
    exact ⟨z, rfl, rfl⟩
  · rintro ⟨z, rfl, rfl⟩
    simp [mod2V]

inductive Tm where
  | lit (z : Int)
  | var (n : Nat)
  | mod2 (a : Tm)
  deriving Inhabited

def ev (ρ : Nat → Int) : Tm → Option Val
  | .lit z => some (vint.inj z)
  | .var n => some (vint.inj (ρ n))
  | .mod2 a => mod2V (ev ρ a)

@[reducible] def sem : Kanon.Sem where
  Term := Tm
  Ty := Unit
  Val := Val
  Env := Nat → Int
  ty _ := ()
  WT _ := True
  ev := ev
  size _ := 0

theorem ev_lit {ρ : Nat → Int} {z : Int} : ev ρ (.lit z) = some (vint.inj z) := rfl
theorem ev_mod2 {ρ : Nat → Int} {a : Tm} : ev ρ (.mod2 a) = mod2V (ev ρ a) := rfl

theorem ev_cases {ρ : Nat → Int} {t : Tm} : ev ρ t = none ∨ ∃ z, ev ρ t = some (vint.inj z) := by
  induction t with
  | lit z => exact .inr ⟨z, rfl⟩
  | var n => exact .inr ⟨ρ n, rfl⟩
  | mod2 a ih =>
    rw [ev_mod2]
    rcases ih with h | ⟨z, h⟩ <;> rw [h]
    · exact .inl rfl
    · exact .inr ⟨z % 2, rfl⟩

/-- The terms whose values are surely even. -/
def isEven : Tm → Bool
  | .lit z => z % 2 == 0
  | _ => false

theorem isEven_ev {t : Tm} (h : isEven t = true) {ρ : Nat → Int} {z : Int}
    (e : ev ρ t = some (vint.inj z)) : z % 2 = 0 := by
  cases t with
  | lit z' =>
    simp only [ev_lit, Option.some.injEq, Embed.inj_eq_iff] at e
    subst e
    simpa [isEven] using h
  | _ => simp [isEven] at h

attribute [kanon_ev] ev_lit ev_mod2
attribute [kanon_val] mod2V_eq_some
attribute [kanon_atom_cases] ev_cases
attribute [kanon_close_lemma] isEven_ev

example (t : Tm) (h : isEven t = true) : sem.Refines (.mod2 t) (.lit 0) := by
  refine Sem.Refines.intro (fun _ => ⟨trivial, rfl⟩) ?_
  kanon_sem_core
  all_goals kanon_close_lemmas

end KanonTest.CasesAtom
