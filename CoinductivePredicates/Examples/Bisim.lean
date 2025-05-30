import CoinductivePredicates.Basic

set_option trace.Elab.coinductive true

namespace Test

structure FSM where
  S : Type
  d : S → Nat → S
  A : S → Prop

coinductive Bisim (fsm : FSM) : fsm.S → fsm.S → Prop :=
  | step {s t : fsm.S} :
    (fsm.A s ↔ fsm.A t)
    → (∀ c, Bisim (fsm.d s c) (fsm.d t c))
    → Bisim fsm s t

macro "coinduction " "using" P:term "with" ids:(ppSpace colGt ident)+ : tactic =>
  let ids := ids
  `(tactic| (exists $P; constructor; intro $ids*))

theorem bisim_refl : Bisim f a a := by
  exists fun a b => a = b
  simp only [and_true]
  intro s t seqt
  rw [seqt]
  exact .step (Eq.to_iff rfl) (congrFun rfl)


theorem bisim_refl' : Bisim f a a := by
  coinduction using (· = ·) with s t h_Rst
  · rw [h_Rst]
    exact .step (by rfl) (fun c => rfl)
  · rfl

theorem bisim_symm (h : Bisim f a b): Bisim f b a := by
  rcases h with ⟨rel, relIsBisim, rab⟩
  exists fun a b => rel b a
  simp_all
  intro a b holds
  specialize relIsBisim holds
  rcases relIsBisim with ⟨iff, v⟩
  exact Bisim.Invariant.step (id (Iff.symm iff)) fun c => v c

theorem Bisim.unfold {f} : Bisim.Is f (Bisim f) := by
  rintro s t ⟨R, h_is, h_Rst⟩
  constructor
  · exact (h_is h_Rst).1
  · intro c; exact ⟨R, h_is, (h_is h_Rst).2 c⟩

-- case principle!
@[elab_as_elim]
def Bisim.casesOn {f : FSM} {s t}
    {motive : Bisim f s t → Prop}
    (h : Bisim f s t)
    (step : ∀ {s t}, (f.A s ↔ f.A t)
      → (∀ c, Bisim f (f.d s c) (f.d t c)) → motive h) :
    motive h := by
  have ⟨R, h_is, h_R⟩ := h
  have ⟨h₁, h₂⟩ := h_is h_R
  apply step h₁ (fun c => ⟨R, h_is, h₂ c⟩)

theorem bisim_trans (h_ab : Bisim f a b) (h_bc : Bisim f b c) :
    Bisim f a c := by
  coinduction
    using (fun s t => ∃ u, Bisim f s u ∧ Bisim f u t)
    with s t h_Rst
  · rcases h_Rst with ⟨u, h_su, h_ut⟩
    have ⟨h_su₁, h_su₂⟩ := h_su.unfold
    have ⟨h_ut₁, h_ut₂⟩ := h_ut.unfold
    refine ⟨?_, ?_⟩
    · rw [h_su₁, h_ut₁]
    · intro c; exact ⟨_, h_su₂ c, h_ut₂ c⟩
  · exact ⟨b, h_ab, h_bc⟩

/-- info: 'Test.bisim_trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bisim_trans
/-- info: 'Test.bisim_symm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bisim_symm
/-- info: 'Test.bisim_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bisim_refl

