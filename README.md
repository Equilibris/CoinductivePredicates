# CoinductivePredicates

A very simple implementation of coinductive-predicates.
Idea by [@bollu](https://github.com/bollu) , dualized by [@alexkeizer](https://github.com/alexkeizer).

For an explanation of how this works please see [this blog post](https://pixel-druid.com/articles/inductive-predicate-as-least-fixed-point-directly) .
In this repository we simply dualize it and make it work for inductives.

# Usage example

This is all detailed in CoinductivePredicates/Examples:

```lean
structure FSM where
  S : Type
  d : S → Nat → S
  A : S → Prop

coinductive Bisim (fsm : FSM) : fsm.S → fsm.S → Prop :=
  | step {s t : fsm.S} :
    (fsm.A s ↔ fsm.A t)
    → (∀ c, Bisim (fsm.d s c) (fsm.d t c))
    → Bisim fsm s t
```

Which then is equivlient to

```lean
inductive Bisim.Invariant (fsm : FSM) (Bisim : fsm.S → fsm.S → Prop) (x y fsm.S) : Prop where
  | step :
    (fsm.A x ↔ fsm.A y)
    → (∀ c, Bisim (fsm.d x c) (fsm.d y c))
    → Bisim.Invariant fsm Bisim x y

abbrev Bisim.Is (fsm : FSM) (R : fsm.S → fsm.S → Prop) : Prop :=
  ∀ {x y}, R x y → Bisim.Invariant fsm R x y

def Bisim (fsm : FSM) : fsm.S → fsm.S → Prop :=
  fun x y => ∃ R, @Bisim.Is fsm R ∧ R x y

```

