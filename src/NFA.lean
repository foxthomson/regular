import data.fintype.basic
import data.set.lattice
import DFA
import fixpoint

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

structure ε_NFA := 
(alphabet : Type u) 
[alphabet_fintype : fintype alphabet]
(state : Type v)
[state_fintype : fintype state]
(step : state → option alphabet → set state)
(start : set state)
(accept_states : set state)

namespace ε_NFA

instance fin₁ (M : ε_NFA) : fintype M.alphabet := M.alphabet_fintype
instance fin₂ (M : ε_NFA) : fintype M.state := M.state_fintype

open least_fixpoint

inductive in_ε_closure (M : ε_NFA) : set M.state → M.state → Prop
| base : ∀ Ss (S ∈ Ss), in_ε_closure Ss S
| step : ∀ Ss S (h : in_ε_closure Ss S), in_ε_closure (Ss >>= (λ (T : M.state), M.step T option.none)) S

inductive ε_closure (M : ε_NFA) : set M.state → M.state → Prop
| base : ∀ Ss (S ∈ Ss), ε_closure Ss S
| step : ∀ Ss S T, ε_closure Ss S → T ∈ M.step S option.none → ε_closure Ss T

-- def ε_closure (M : ε_NFA) (Ss : set M.state) : set M.state :=
-- set_of (least_fixpoint (λ Ts, Ts ∪ (Ts >>= (λ (T : M.state), M.step T option.none))) Ss)

-- @[simp] lemma ε_closure_of_ε_closure (M : ε_NFA) :
--   ∀ (Ss : set M.state), M.ε_closure (M.ε_closure Ss) = M.ε_closure Ss := 
-- -- fixpoint_of_fixpoint _ begin simp end
-- begin
--   intro Ss,
--   ext S,
--   split,
--   { intro h,
--     type_check ε_closure.rec_on h,
--     -- generalize_hyp ha : M.ε_closure Ss = a at h,
--     -- apply ε_closure.base,
--     induction h with _ _ _ Ss S' T hT h ih,
--     { finish },
--     {  } },
--   { intro h,
--     apply ε_closure.base,
--     assumption }
-- end

def step_set (M : ε_NFA) : set M.state → M.alphabet → set M.state :=
λ Ss a, M.ε_closure $ Ss >>= λ S, M.step S (option.some a)

def eval (M : ε_NFA) : list M.alphabet → set M.state := list.foldl M.step_set (M.ε_closure M.start)

def accepts (M : ε_NFA) (s : list M.alphabet) : Prop :=
∃ S ∈ M.accept_states, S ∈ M.eval s

def NFA_of_ε_NFA (M : ε_NFA) : NFA :=
{ alphabet := M.alphabet,
  state := M.state,
  step := λ S a, M.ε_closure (M.step S (some a)),
  start := M.ε_closure M.start,
  accept_states := M.accept_states }

lemma NFA_of_ε_NFA_step_set_match (M : ε_NFA) (Ss : set M.state) (a : M.alphabet) :
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

lemma NFA_of_ε_NFA_eval_match (M : ε_NFA) (s : list M.alphabet) :
  M.eval s = (NFA_of_ε_NFA M).eval s :=
begin
  change list.foldl M.step_set (M.ε_closure M.start) s = list.foldl M.NFA_of_ε_NFA.step_set (M.ε_closure M.start) s,
  congr,
  ext1,
  ext1,
  rw NFA_of_ε_NFA_step_set_match
end

lemma NFA_of_ε_NFA_correct (M : ε_NFA) (s : list M.alphabet) :
  M.accepts s ↔ M.NFA_of_ε_NFA.accepts s :=
begin
  rw [accepts, NFA.accepts, NFA_of_ε_NFA_eval_match],
  tauto
end

end ε_NFA
