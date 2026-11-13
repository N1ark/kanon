import KanonCore.Proof

/-! `kanon_sem_core` reduces the equations of injected values that it leaves,
`vint.inj a = vint.inj b`, and substitutes them. -/

namespace KanonTest.SemInj

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

/-- The values that are integers, which the atoms evaluate to. -/
def IsInt (v : Val) : Prop := ∃ z, v = vint.inj z

/-- The negation of a value. -/
def negV (o : Option Val) : Option Val := o.bind fun x => (vint.proj x).map fun z => vint.inj (-z)

theorem negV_eq_some {o : Option Val} {r : Val} :
    negV o = some r ↔ ∃ z, o = some (vint.inj z) ∧ r = vint.inj (-z) := by
  constructor
  · intro h
    simp only [negV, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      Embed.proj_eq_some_iff] at h
    obtain ⟨_, rfl, z, rfl, rfl⟩ := h
    exact ⟨z, rfl, rfl⟩
  · rintro ⟨z, rfl, rfl⟩
    simp [negV]

inductive Tm where
  | var (n : Nat)
  | neg (a : Tm)
  deriving Inhabited

def ev (ρ : Nat → Val) : Tm → Option Val
  | .var n => match ρ n with
    | .int z => some (.int z)
    | _ => none
  | .neg a => negV (ev ρ a)

@[reducible] def sem : Kanon.Sem where
  Term := Tm
  Ty := Unit
  Val := Val
  Env := Nat → Val
  ty _ := ()
  WT _ := True
  ev := ev
  size _ := 0

theorem ev_neg {ρ : Nat → Val} {a : Tm} : ev ρ (.neg a) = negV (ev ρ a) := rfl

theorem ev_cases {ρ : Nat → Val} {t : Tm} : ev ρ t = none ∨ ∃ v, ev ρ t = some v ∧ IsInt v := by
  induction t with
  | var n => unfold ev; split <;> simp [IsInt, vint]
  | neg a ih =>
    rcases ih with h | ⟨v, h, z, rfl⟩
    · exact .inl (by rw [ev_neg, h]; rfl)
    · exact .inr ⟨_, by rw [ev_neg, h]; rfl, -z, rfl⟩

attribute [kanon_ev] ev_neg
attribute [kanon_val] IsInt negV_eq_some
attribute [kanon_atom_cases] ev_cases

example (t : Tm) : sem.Refines (.neg (.neg t)) t := by
  refine Sem.Refines.intro (fun _ => ⟨trivial, rfl⟩) ?_
  kanon_sem_core
  -- the values of the atom are `vint.inj a`, of `e` and `IsInt` both: `a` is
  -- the integer of both
  all_goals omega

end KanonTest.SemInj
