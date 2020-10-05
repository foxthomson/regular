import data.fintype.basic
import data.set.lattice
import DFA

universes u v

structure NFA := 
(alphabet : Type u) 
[alphabet_fintype : fintype alphabet]
(state : Type v)
[state_fintype : fintype state]
(step : state → alphabet → set state)
(start : set state)
(accept_states : set state)

namespace NFA

@[reducible] def start_dec (M : NFA) := decidable_pred M.start
@[reducible] def step_dec (M : NFA) := Π (S : M.state) (a : M.alphabet), decidable_pred (M.step S a)

instance fin₁ (M : NFA) : fintype M.alphabet := M.alphabet_fintype
instance fin₂ (M : NFA) : fintype M.state := M.state_fintype

def step_set (M : NFA) : set M.state → M.alphabet → set M.state :=
λ Ss a, Ss >>= λ S, M.step S a

instance step_set_dec (M : NFA) (a : M.alphabet) [M.step_dec] :
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

def eval (M : NFA) : list M.alphabet → set M.state := list.foldl M.step_set M.start

instance eval_dec (M : NFA) (s : list M.alphabet) [hdec : M.start_dec] [M.step_dec] : 
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

def accepts (M : NFA) (s : list M.alphabet) : Prop :=
∃ S ∈ M.accept_states, S ∈ M.eval s

def NFA_of_DFA (M : DFA) : NFA :=
{ alphabet := M.alphabet,
  alphabet_fintype := M.alphabet_fintype,
  state := M.state,
  state_fintype := M.state_fintype,
  step := λ S a, {M.step S a},
  start := {M.start},
  accept_states := M.accept_states }

lemma NFA_of_DFA_eval_match (M : DFA) (s : list M.alphabet) :
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

lemma NFA_of_DFA_correct (M : DFA) (s : list M.alphabet) :
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

def DFA_of_NFA (M : NFA) : DFA :=
{ alphabet := M.alphabet,
  alphabet_fintype := M.alphabet_fintype,
  state := set M.state,
  state_fintype := set.fintype,
  step := M.step_set,
  start := M.start,
  accept_states := {Ss : set M.state | ∃ (S ∈ M.accept_states), S ∈ Ss} }

lemma DFA_of_NFA_correct (M : NFA) (s : list M.alphabet) :
  M.accepts s ↔ M.DFA_of_NFA.accepts s := by refl

end NFA
