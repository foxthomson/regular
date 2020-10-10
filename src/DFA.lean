import data.fintype.basic

universes u v

variable {α : Type u}

structure DFA (alphabet : Type u) :=
[alphabet_fintype : fintype alphabet]
(state : Type v)
[state_fintype : fintype state]
(step : state → alphabet → state)
(start : state)
(accept_states : set state)

namespace DFA

def eval (M : DFA α) : list α → M.state :=
list.foldl M.step M.start

def accepts (M : DFA α) (s : list α) : Prop :=
M.eval s ∈ M.accept_states

end DFA