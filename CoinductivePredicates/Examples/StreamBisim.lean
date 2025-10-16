import CoinductivePredicates.Basic

def S (a : Type _) := Nat → a
def S.dest (x : S a) : a × S a := ⟨x 0, x ∘ Nat.succ⟩

coinductive Bisim (a : Type _) : a × S a → a × S a → Prop where
  | step : Bisim u.dest v.dest → Bisim a ⟨x, u⟩ ⟨x, v⟩

namespace Bisim
def step {x : a} {u v : S a} (h : Bisim a u.dest v.dest) : Bisim a ⟨x, u⟩ ⟨x, v⟩ := by
  rcases h with ⟨h, hIs, hHold⟩
  refine ⟨fun a b => h a b ∨ (a = ⟨x, u⟩ ∧ b = ⟨x, v⟩), ?_, .inr ⟨rfl, rfl⟩⟩
  intro x y hxy
  rcases hxy with (h|⟨rfl, rfl⟩)
  · rcases hIs h with ⟨this⟩
    refine .step (.inl this)
  · refine .step (.inl hHold)

def unfold : Bisim.Is a (Bisim a) :=
  fun ⟨R, hIs, hRst⟩ => match hIs hRst with
    | .step z => .step ⟨R, hIs, z⟩

def refl x : Bisim a x x := ⟨
  Eq,
  fun e => e.subst $ .step rfl,
  rfl
⟩

def symm : Bisim a x y → Bisim a y x :=
  fun ⟨R, hIs, hRst⟩ => ⟨
    fun a b => R b a,
    fun hab => by
      rcases hIs hab with ⟨h⟩
      exact .step h,
    hRst,
  ⟩

def trans : Bisim a x y → Bisim a y z → Bisim a x z :=
  fun ⟨Rxy, hxyIs, hxyRst⟩ ⟨Ryz, hyzIs, hyzRst⟩ => ⟨
    fun a c => ∃ b, Rxy a b ∧ Ryz b c,
    fun ⟨y, hxy, hyz⟩ => by
      rcases hxyIs hxy with ⟨h₁⟩
      rcases hyzIs hyz with ⟨h₂⟩
      exact .step ⟨_, h₁, h₂⟩,
    ⟨y, hxyRst, hyzRst⟩
  ⟩

/- def force (h : Bisim.Is a r) (hxy : r x y) : x = y := by -/
/-   dsimp [Is] at h -/
/-   specialize h hxy -/
/-   rcases h -/
/-   apply (Prod.mk.injEq _ _ _ _).mpr ⟨rfl⟩ -/
/-   apply funext -/
/-   intro n -/
/-   induction n -/
/-   · sorry -/
/-   · sorry -/

def frwd_lemma
    {u v : S a} (n : Nat) (h : Bisim a (u n, (u $ n + ·.succ)) (v n, (v $ n + ·.succ)))
    : u n = v n := by
  generalize u n = x, v n = y at h
  have := h.unfold
  cases this
  rfl

def frwd (h : Bisim a x y) : x = y := by
  rcases h.unfold with ⟨hDest⟩
  rename_i u v
  simp only [Prod.mk.injEq, true_and]
  apply funext
  intro n
  apply frwd_lemma
  induction n
  · repeat conv in 0 + _ => rw [Nat.zero_add]
    exact hDest
  case succ n ih =>
    have := ih.unfold
    generalize  u n = x, v n = y at this
    rcases this with ⟨h⟩
    simp only [S.dest, Nat.succ_eq_add_one, Nat.zero_add, ] at h
    have (f : S a) :
        (fun x => f (n + (x + 1))) ∘ Nat.succ = fun x => f (n + 1 + x.succ) :=
      funext fun x => by dsimp; congr 1; omega
    rw [this u, this v] at h
    exact h

