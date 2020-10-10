import data.fintype.basic
import data.set.lattice
import DFA

universes u v

variable {α : Type}

structure NFA (alphabet : Type u) := 
[alphabet_fintype : fintype alphabet]
(state : Type v)
[state_fintype : fintype state]
(step : state → alphabet → set state)
(start : set state)
(accept_states : set state)

namespace NFA

@[reducible] def start_dec (M : NFA α) := decidable_pred M.start
@[reducible] def step_dec (M : NFA α) := Π (S : M.state) (a : α), decidable_pred (M.step S a)

instance fin₁ (M : NFA α) : fintype α := M.alphabet_fintype
instance fin₂ (M : NFA α) : fintype M.state := M.state_fintype

def step_set (M : NFA α) : set M.state → α → set M.state :=
λ Ss a, Ss >>= λ S, M.step S a

instance step_set_dec (M : NFA α) (a : α) [M.step_dec] :
Π (Ss : set M.state) [decidable_pred Ss], decidable_pred (M.step_set Ss a) :=
begin
  intro Ss,
  introI h,
  intro S,
  rw step_set,
  change decidable (S ∈ (Ss >>= λ (S : M.state), M.step S a)),
  rw [set.bind_def, set.mem_Union],
  apply @fintype.decidable_exists_fintype _ _ _,
  intro T,
  rw [set.mem_Union, exists_prop],
  apply and.decidable
end

def eval (M : NFA α) : list α → set M.state := list.foldl M.step_set M.start

instance eval_dec (M : NFA α) (s : list α) [hdec : M.start_dec] [M.step_dec] : 
decidable_pred (M.eval s) :=
begin
  rw eval,
  tactic.unfreeze_local_instances,
  revert hdec,
  change Π [hdec : decidable_pred M.start], decidable_pred (list.foldl M.step_set M.start s),
  generalize : M.start = start,
  revert start,
  induction s with a s ih;
  tauto
end

def accepts (M : NFA α) (s : list α) : Prop :=
∃ S ∈ M.accept_states, S ∈ M.eval s

def NFA_of_DFA (M : DFA α) : NFA α :=
{ alphabet_fintype := M.alphabet_fintype,
  state := M.state,
  state_fintype := M.state_fintype,
  step := λ S a, {M.step S a},
  start := {M.start},
  accept_states := M.accept_states }

lemma NFA_of_DFA_eval_match (M : DFA α) (s : list α) :
  {M.eval s} = (NFA_of_DFA M).eval s :=
begin
  change {list.foldl M.step M.start s} = list.foldl (NFA_of_DFA M).step_set {M.start} s,
  generalize : M.start = start,
  revert start,
  induction s with a s ih,
  { tauto },
  { intro start,
    rw [list.foldl, list.foldl],
    have : (NFA_of_DFA M).step_set {start} a = {M.step start a},
    { rw step_set,
      finish },
    rw this,
    tauto }
end

lemma NFA_of_DFA_correct (M : DFA α) (s : list α) :
  M.accepts s ↔ (NFA_of_DFA M).accepts s :=
begin
  rw [accepts, DFA.accepts, ←NFA_of_DFA_eval_match],
  split,
  { intro h,
    use M.eval s,
    tauto },
  { rintro ⟨ S, hS₁, hS₂ ⟩,
    rw set.mem_singleton_iff at hS₂,
    rw hS₂ at hS₁,
    assumption }
end

def DFA_of_NFA (M : NFA α) : DFA α :=
{ alphabet_fintype := M.alphabet_fintype,
  state := set M.state,
  state_fintype := set.fintype,
  step := M.step_set,
  start := M.start,
  accept_states := {Ss : set M.state | ∃ (S ∈ M.accept_states), S ∈ Ss} }

lemma DFA_of_NFA_correct (M : NFA α) (s : list α) :
  M.accepts s ↔ M.DFA_of_NFA.accepts s := by refl

end NFA

structure ε_NFA (alphabet : Type u) :=
[alphabet_fintype : fintype alphabet]
(state : Type v)
[state_fintype : fintype state]
(step : state → option alphabet → set state)
(start : set state)
(accept_states : set state)

namespace ε_NFA

instance fin₁ (M : ε_NFA α) : fintype α := M.alphabet_fintype
instance fin₂ (M : ε_NFA α) : fintype M.state := M.state_fintype

inductive ε_closure (M : ε_NFA α) : set M.state → M.state → Prop
| base : ∀ Ss (S ∈ Ss), ε_closure Ss S
| step : ∀ Ss S T, ε_closure Ss S → T ∈ M.step S option.none → ε_closure Ss T

def step_set (M : ε_NFA α) : set M.state → α → set M.state :=
λ Ss a, M.ε_closure $ Ss >>= λ S, M.step S (option.some a)

def eval (M : ε_NFA α) : list α → set M.state := list.foldl M.step_set (M.ε_closure M.start)

def accepts (M : ε_NFA α) (s : list α) : Prop :=
∃ S ∈ M.accept_states, S ∈ M.eval s

def NFA_of_ε_NFA (M : ε_NFA α) : NFA α :=
{ alphabet_fintype := M.alphabet_fintype,
  state := M.state,
  step := λ S a, M.ε_closure (M.step S (some a)),
  start := M.ε_closure M.start,
  accept_states := M.accept_states }

lemma NFA_of_ε_NFA_step_set_match (M : ε_NFA α) (Ss : set M.state) (a : α) :
  M.step_set Ss a = M.NFA_of_ε_NFA.step_set Ss a :=
begin
  rw [step_set, NFA.step_set],
  simp, 
  change M.ε_closure (⋃ (i : M.state) (H : i ∈ Ss), M.step i (some a)) = ⋃ (i : M.NFA_of_ε_NFA.state) (H : i ∈ Ss), M.ε_closure (M.step i (some a)),
  ext b,
  split,
  { intro h,   
    generalize_hyp hT : (⋃ (i : M.state) (H : i ∈ Ss), M.step i (some a)) = Ts at h,
    induction h with _ _ h Us U T hU h ih,
    { rw ←hT at h,
      simp only [exists_prop, set.mem_Union] at h ⊢,
      cases h with i hi,
      use i,
      use hi.1,
      apply ε_closure.base,
      tauto },
    { simp only [exists_prop, set.mem_Union] at *,
      specialize ih hT,
      cases ih with i ih,
      existsi i,
      existsi ih.1,
      apply ε_closure.step,
      use ih.2,
      assumption } },
  { rintro ⟨ _, ⟨ ⟨ S, rfl ⟩, hb ⟩ ⟩,
    simp only [exists_prop, set.mem_Union] at hb,
    cases hb with hS h,
    generalize_hyp hT : M.step S (some a) = T at h,
    induction h,
    { apply ε_closure.base,
      finish },
    { specialize h_ih hT,
      apply ε_closure.step,
      assumption' } }
end

lemma NFA_of_ε_NFA_eval_match (M : ε_NFA α) (s : list α) :
  M.eval s = (NFA_of_ε_NFA M).eval s :=
begin
  change list.foldl M.step_set (M.ε_closure M.start) s = list.foldl M.NFA_of_ε_NFA.step_set (M.ε_closure M.start) s,
  congr,
  ext1,
  ext1,
  rw NFA_of_ε_NFA_step_set_match
end

lemma NFA_of_ε_NFA_correct (M : ε_NFA α) (s : list α) :
  M.accepts s ↔ M.NFA_of_ε_NFA.accepts s :=
begin
  rw [accepts, NFA.accepts, NFA_of_ε_NFA_eval_match],
  tauto
end

end ε_NFA
