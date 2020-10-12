import data.fintype.basic
import data.set.lattice
import DFA

universes u v

variable {α : Type}

structure NFA (alphabet : Type u) := 
[alphabet_fintype : fintype alphabet]
(state : Type v)
[state_fintype : fintype state]
[state_dec : decidable_eq state]
(step : state → alphabet → finset state)
(start : finset state)
(accept_states : finset state)
namespace NFA

-- @[reducible] def start_dec (M : NFA α) := decidable_pred M.start
-- @[reducible] def step_dec (M : NFA α) := Π (S : M.state) (a : α), decidable_pred (M.step S a)
-- instance dec₁ (M : NFA α) := M.start_dec
-- instance dec₂ (M : NFA α) := M.step_dec
-- instance dec₃ (M : NFA α) := M.accept_dec
instance dec (M : NFA α) := M.state_dec

instance fin₁ (M : NFA α) := M.alphabet_fintype
instance fin₂ (M : NFA α) := M.state_fintype

def step_set (M : NFA α) : finset M.state → α → finset M.state :=
λ Ss a, finset.bind Ss (λ S, (M.step S a))

def eval (M : NFA α) : list α → finset M.state := list.foldl M.step_set M.start

def accepts (M : NFA α) (s : list α) : Prop :=
∃ S ∈ M.accept_states, S ∈ M.eval s

def NFA_of_DFA (M : DFA α) : NFA α :=
{ alphabet_fintype := M.alphabet_fintype,
  state := M.state,
  state_fintype := M.state_fintype,
  step := λ S a, {M.step S a},
  start := {M.start},
  accept_states := M.accept_states }

lemma NFA_of_DFA_eval_match (M : DFA α) [decidable_eq M.state] (s : list α) :
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
    finish },
  { rintro ⟨ S, hS₁, hS₂ ⟩,
    rw finset.mem_singleton at hS₂,
    rw hS₂ at hS₁,
    assumption }
end

def DFA_of_NFA (M : NFA α) : DFA α :=
{ alphabet_fintype := M.alphabet_fintype,
  state := finset M.state,
  step := M.step_set,
  start := M.start,
  accept_states := finset.univ.filter (λ S, ∃ s ∈ S, s ∈ M.accept_states) }

lemma DFA_of_NFA_correct (M : NFA α) (s : list α) :
  M.accepts s ↔ M.DFA_of_NFA.accepts s :=
begin
  rw [accepts, DFA.accepts, eval, DFA.eval],
  change (∃ (S : M.state) (H : S ∈ M.accept_states), S ∈ list.foldl M.step_set M.start s) ↔ list.foldl M.step_set M.start s ∈ finset.univ.filter (λ S : finset M.state, ∃ s ∈ S, s ∈ M.accept_states),
  rw finset.mem_filter,
  finish
end

end NFA

structure ε_NFA (alphabet : Type u) :=
[alphabet_fintype : fintype alphabet]
(state : Type v)
[state_fintype : fintype state]
[state_dec : decidable_eq state]
(step : state → option alphabet → finset state)
(start : finset state)
(accept_states : finset state)

namespace ε_NFA

instance dec (M : ε_NFA α) := M.state_dec

instance fin₁ (M : ε_NFA α) : fintype α := M.alphabet_fintype
instance fin₂ (M : ε_NFA α) : fintype M.state := M.state_fintype

inductive ε_closure_set (M : ε_NFA α) : finset M.state → M.state → Prop
| base : ∀ Ss (S ∈ Ss), ε_closure_set Ss S
| step : ∀ Ss S T, ε_closure_set Ss S → T ∈ M.step S option.none → ε_closure_set Ss T

def ε_closure (M : ε_NFA α) (S : finset M.state) : finset M.state :=
  (λ T : finset M.state, S ∪ (T.bind (λ t, M.step t none)))^[fintype.card M.state] S

def step_set (M : ε_NFA α) : finset M.state → α → finset M.state :=
λ Ss a, M.ε_closure $ finset.bind Ss (λ S, M.step S (option.some a))

def eval (M : ε_NFA α) : list α → finset M.state := 
  list.foldl M.step_set (M.ε_closure M.start)

def accepts (M : ε_NFA α) (s : list α) : Prop :=
∃ S ∈ M.accept_states, S ∈ M.eval s

def NFA_of_ε_NFA (M : ε_NFA α) : NFA α :=
{ alphabet_fintype := M.alphabet_fintype,
  state := M.state,
  step := λ S a, M.ε_closure (M.step S (some a)),
  start := M.ε_closure M.start,
  accept_states := M.accept_states }

lemma NFA_of_ε_NFA_step_set_match (M : ε_NFA α) (Ss : finset M.state) (a : α) :
  M.step_set Ss a = M.NFA_of_ε_NFA.step_set Ss a :=
begin
  sorry
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
