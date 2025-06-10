import CoinductivePredicates.Basic

def S (a : Type _) := Nat → a
def S.dest (x : S a) : a × S a := ⟨x 0, x ∘ Nat.succ⟩

coinductive Bisim (a : Type _) : a × S a → a × S a → Prop where
  | step : Bisim u.dest v.dest → Bisim a ⟨x, u⟩ ⟨x, v⟩

theorem bisim_refl : Bisim f a a := ⟨
  (· = · ),
  -- I want to remove the first two rfls
  fun heq => heq.subst $ .step rfl,
  rfl
⟩
