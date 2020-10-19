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

def step_set' (M : ε_NFA α) : finset M.state → option α → finset M.state :=
λ Ss a, finset.bind Ss (λ S, M.step S a)

inductive ε_closure_set (M : ε_NFA α) (Ss : finset M.state) : M.state → Prop
| base : ∀ (S ∈ Ss), ε_closure_set S
| step : ∀ S T, ε_closure_set S → T ∈ M.step S option.none → ε_closure_set T

def sub_of_compl {β : Type u} [fintype β] [decidable_eq β] : ∀ T U : finset β, Tᶜ ⊆ Uᶜ → U ⊆ T :=
begin
  intros T U h x hxU,
  by_contra hTc,
  rw ←finset.mem_compl at hTc,
  have hUc := finset.mem_of_subset h hTc,
  finish
end

instance ε_NFA_has_well_founded {β : Type u} [fintype β] [decidable_eq β] : has_well_founded (finset β) :=
{ r := (λ S₁ S₂ : finset β, S₁ᶜ < S₂ᶜ), 
  wf := 
  inv_image.wf _ finset.lt_wf } 

def ε_closure (M : ε_NFA α) : finset M.state → finset M.state
| S :=
begin
  let S' := S ∪ M.step_set' S none,
  by_cases heq : S' = S,
  { exact S },
  { let : S'ᶜ < Sᶜ,
    { have hsub : S'ᶜ ⊆ Sᶜ,
      { intros s hs,
        rw finset.mem_compl at hs ⊢,
        finish },
      use hsub,
      { intro hS,
        apply heq, 
        rw finset.subset.antisymm_iff,
        split;
        apply sub_of_compl;
        assumption } }, 
    exact ε_closure S' }
end
using_well_founded {dec_tac := tactic.assumption}

lemma step_set'_wf (M : ε_NFA α) (S : finset M.state) (hneq : S ∪ M.step_set' S none ≠ S) :
  (S ∪ M.step_set' S none)ᶜ < Sᶜ :=
begin
  have hsub : (S ∪ M.step_set' S none)ᶜ ⊆ Sᶜ,
  { intros s hs,
    rw finset.mem_compl at hs ⊢,
    finish },
  use hsub,
  intro hS,
  apply hneq, 
  rw finset.subset.antisymm_iff,
  split;
  apply sub_of_compl,
  assumption'
end

lemma ε_closure_equiv_ε_closure_set (M : ε_NFA α) :
  Π (S : finset M.state) (s : M.state), s ∈ M.ε_closure S ↔ M.ε_closure_set S s
| S :=
begin
  have IH := λ T (h : Tᶜ < Sᶜ), ε_closure_equiv_ε_closure_set T,
  intro s,
  split,
  { intro h,
    rw ε_closure at h,
    dsimp at h,
    split_ifs at h with heq,
    { apply ε_closure_set.base,
      assumption },
    { have hwf : (S ∪ M.step_set' S none)ᶜ < Sᶜ := M.step_set'_wf S heq,
      have h' : M.ε_closure_set (S ∪ M.step_set' S none) s,
        rwa ← IH (S ∪ M.step_set' S none) hwf,
      induction h' with t ht t' t d e ih,
      { simp at ht,
        cases ht,
        { apply ε_closure_set.base,
          assumption },
        { rw step_set' at ht,
          simp only [exists_prop, finset.mem_bind] at ht,
          cases ht with t' ht,
          apply ε_closure_set.step t' t,
          { apply ε_closure_set.base,
            tauto },
          { tauto } } },
      { apply ε_closure_set.step t' t,
        { apply ih,
          rwa IH (S ∪ M.step_set' S none) hwf },
        assumption } } },
  { intro h,
    rw ε_closure,
    dsimp,
    split_ifs with heq;
    induction h with t ht t' t ht' ht ih,
    { assumption },
    { rw ←heq,
      simp only [finset.mem_union],
      right,
      rw step_set',
      simp only [exists_prop, finset.mem_bind],
      use t',
      tauto },
    all_goals
    { have hwf : (S ∪ M.step_set' S none)ᶜ < Sᶜ := M.step_set'_wf S heq },
    { rw IH (S ∪ M.step_set' S none) hwf,
      apply ε_closure_set.base,
      rw finset.mem_union,
      left,
      assumption },
    { rw IH (S ∪ M.step_set' S none) hwf,
      apply ε_closure_set.step t' t,
      rwa ←IH (S ∪ M.step_set' S none) hwf,
      assumption } }
end
using_well_founded {dec_tac := tactic.assumption}

def step_set (M : ε_NFA α) : finset M.state → α → finset M.state :=
λ Ss a, M.ε_closure $ finset.bind Ss (λ S, M.step S (option.some a))

def eval (M : ε_NFA α) : list α → finset M.state := 
  list.foldl M.step_set (M.ε_closure M.start)

def accepts (M : ε_NFA α) (s : list α) : Prop :=
∃ S ∈ M.accept_states, S ∈ M.eval s

instance accepts_dec (M : ε_NFA α) : decidable_pred M.accepts :=
begin
  intro s,
  exact fintype.decidable_exists_fintype
end

def NFA_of_ε_NFA (M : ε_NFA α) : NFA α :=
{ alphabet_fintype := M.alphabet_fintype,
  state := M.state,
  step := λ S a, M.ε_closure (M.step S (some a)),
  start := M.ε_closure M.start,
  accept_states := M.accept_states }

lemma NFA_of_ε_NFA_step_set_match (M : ε_NFA α) (Ss : finset M.state) (a : α) :
  M.step_set Ss a = M.NFA_of_ε_NFA.step_set Ss a :=
begin
  rw [step_set, NFA.step_set],
  simp,
  ext b,
  rw ε_closure_equiv_ε_closure_set,
  split,
  { intro h,
    -- generalize_hyp hT : (Ss.bind (λ (S : M.state), M.step S (some a))) = Ts at h,
    induction h with s h U T hU h ih,
    { 
      -- rw ←hT at h,
      simp only [exists_prop, finset.mem_bind] at h ⊢,
      cases h with i hi,
      rw @finset.mem_bind _ M.state M.state_dec,
      use i,
      use hi.1,
      change s ∈ M.ε_closure (M.step i (some a)),
      rw ε_closure_equiv_ε_closure_set,
      apply ε_closure_set.base,
      tauto },
    { rw @finset.mem_bind _ M.state M.state_dec at ⊢ ih,
      rcases ih with ⟨ i, h₁, h₂ ⟩,
      existsi i,
      existsi h₁,
      change T ∈ M.ε_closure (M.step i (some a)),
      rw ε_closure_equiv_ε_closure_set,
      apply ε_closure_set.step U _,
      change U ∈ M.ε_closure (M.step _ (some _)) at h₂,
      rw ←ε_closure_equiv_ε_closure_set,
      assumption' } },
  { rw @finset.mem_bind _ M.state M.state_dec,
    rintro ⟨ s, hsSs, hba ⟩,
    change b ∈ M.ε_closure (M.step _ (some _)) at hba,
    rw ε_closure_equiv_ε_closure_set at hba,
    induction hba with s h U T hU h ih,
    { apply ε_closure_set.base,
      finish },
    { specialize ih,
      apply ε_closure_set.step,
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
