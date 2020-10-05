import data.fintype.basic

universes u v

structure DFA := 
(alphabet : Type u) 
[alphabet_fintype : fintype alphabet]
(state : Type v)
[state_fintype : fintype state]
(step : state → alphabet → state)
(start : state)
(accept_states : set state)

namespace DFA

def eval (M : DFA) : list M.alphabet → M.state :=
list.foldl M.step M.start

def accepts (M : DFA) (s : list M.alphabet) : Prop :=
M.eval s ∈ M.accept_states

end DFA