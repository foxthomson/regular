import data.fintype.basic

structure DFA := 
(alphabet : Type) 
[alphabet_fintype : fintype alphabet]
(state : Type)
[state_fintype : fintype state]
(step : state → alphabet → state)
(start : state)
(accept_states : set state)
[accept_states_dec : decidable_pred accept_states]

namespace DFA

instance (M : DFA) : decidable_pred M.accept_states := M.accept_states_dec

def eval (M : DFA) : list M.alphabet → M.state :=
list.foldl M.step M.start

def accepts (M : DFA) (s : list M.alphabet) : Prop :=
M.eval s ∈ M.accept_states

end DFA