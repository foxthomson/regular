import data.fintype.basic
import data.set.lattice

structure NFA := 
(alphabet : Type) 
[alphabet_fintype : fintype alphabet]
(state : Type)
[state_fintype : fintype state]
(step : state → alphabet → set state)
[step_dec : Π (S : state) (a : alphabet), decidable_pred (step S a)]
(start : set state)
[start_dec : decidable_pred start]
(accept_states : set state)
[accept_states_dec : decidable_pred accept_states]

namespace NFA

instance dec₁ (M : NFA) : decidable_pred M.accept_states := M.accept_states_dec
instance dec₂ (M : NFA) : decidable_pred M.start := M.start_dec
instance dec₃ (M : NFA) : Π (S : M.state) (a : M.alphabet), decidable_pred (M.step S a) := M.step_dec

instance fin₁ (M : NFA) : fintype M.alphabet := M.alphabet_fintype
instance fin₂ (M : NFA) : fintype M.state := M.state_fintype

def step_set (M : NFA) : set M.state → M.alphabet → set M.state :=
λ Ss a, Ss >>= λ S, M.step S a

instance step_set_dec (M : NFA) (a : M.alphabet) :
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

def eval' (M : NFA) (start' : set M.state) : list M.alphabet → set M.state :=
list.foldl M.step_set start'

instance eval'_dec (M : NFA) (start' : set M.state) [decidable_pred start'] (s : list M.alphabet) : 
  decidable_pred (M.eval' start' s) :=
begin
  rw eval',
  tactic.unfreeze_local_instances,
  revert start',
  induction s with a s ih,
  { intros _ h,
    rw list.foldl,
    assumption },
  { intros start' hdec,
    rw list.foldl,
    specialize ih (M.step_set start' a),
    assumption }
end

def eval (M : NFA) : list M.alphabet → set M.state := M.eval' M.start

instance eval_dec (M : NFA) (s : list M.alphabet) : decidable_pred (M.eval s) :=
  M.eval'_dec M.start s

def accepts (M : NFA) (s : list M.alphabet) : bool :=
∃ S ∈ M.accept_states, S ∈ M.eval s

end NFA
