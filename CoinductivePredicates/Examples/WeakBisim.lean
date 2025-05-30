import CoinductivePredicates.Basic

namespace WeakBisimTest

/-- An FSM without input, but with silent/tau steps -/
structure FSM where
  S : Type
  d : S → S
  /-- if `o s = none`, it's a silent step -/
  o : S → Option Bool

coinductive Const (b? : Option Bool) (fsm : FSM) : fsm.S → Prop
  | step {s} :
      fsm.o s = b? → Const (fsm.d s) → Const b? fsm s

/--
info: @[reducible] def WeakBisimTest.Const.Is : Option Bool → (fsm : FSM) → (fsm.S → Prop) → Prop :=
fun b? fsm R => ∀ {x : fsm.S}, R x → Const.Invariant b? fsm R x
-/
#guard_msgs in #print Const.Is

coinductive WeakBisim (fsm : FSM) : fsm.S → fsm.S → Prop :=
  | step {s t : fsm.S} :
    (fsm.o s = fsm.o t)
    → WeakBisim (fsm.d s) (fsm.d t)
    → WeakBisim fsm s t
  | tauLeft {s t : fsm.S} :
    fsm.o s = none → WeakBisim (fsm.d s) t → WeakBisim fsm s t
  | tauRight {s t : fsm.S} :
    fsm.o t = none → WeakBisim s (fsm.d t) → WeakBisim fsm s t

/--
info: def WeakBisimTest.WeakBisim : (fsm : FSM) → fsm.S → fsm.S → Prop :=
fun fsm x x_1 => ∃ R, WeakBisim.Is fsm R ∧ R x x_1
-/
#guard_msgs in #print WeakBisim

/--
info: @[reducible] def WeakBisimTest.WeakBisim.Is : (fsm : FSM) → (fsm.S → fsm.S → Prop) → Prop :=
fun fsm R => ∀ {x x_1 : fsm.S}, R x x_1 → WeakBisim.Invariant fsm R x x_1
-/
#guard_msgs in #print WeakBisim.Is

end WeakBisimTest
