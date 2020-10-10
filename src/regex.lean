import data.fintype.basic
import NFA

universe u

inductive regex (α : Type u) : Type (u+1)
| RZero : regex
| RNull : regex
| RChar : α → regex
| RStar : regex → regex
| RPlus : regex → regex → regex
| RComp : regex → regex → regex

namespace regex

def match_null {α : Type u} : regex α → bool
| RZero := ff
| RNull := tt
| (RChar _) := ff
| (RStar M) := tt
| (RPlus M N) := M.match_null || N.match_null
| (RComp M N) := M.match_null && N.match_null

def feed {α : Type u} [decidable_eq α] : regex α → α → regex α
| RZero _ := RZero
| RNull _ := RZero
| (RChar a₁) a₂ := ite (a₁ = a₂) RNull RZero
| (RStar M) a := RComp (feed M a) (RStar M)
| (RPlus M N) a := RPlus (feed M a) (feed N a)
| (RComp M N) a := 
  ite M.match_null (RPlus (RComp (feed M a) N) (feed N a)) (RComp (feed M a) N)

def bmatch {α : Type u} [decidable_eq α] : regex α → list α → bool
| M [] := match_null M
| M (a::as) := bmatch (M.feed a) as

def ε_NFA_of_regex {α : Type u} [fintype α] [decidable_eq α] : regex α → ε_NFA α
| RZero := 
  { state := pempty,
    step := λ _ _, ∅,
    start := ∅,
    accept_states := ∅ }
| RNull := 
  { state := punit,
    step := λ _ _, ∅,
    start := {punit.star},
    accept_states := {punit.star} }
| (RChar a) := 
  { state := bool,
    step := λ S b, b.cases_on' ∅ (λ b, ite S (ite (a = b) {ff} ∅) ∅),
    start := {tt},
    accept_states := {ff} }
| (RStar P) := 
  let P := P.ε_NFA_of_regex in
  { state := P.state,
    state_fintype := P.state_fintype,
    step := λ S b, b.cases_on' (ite (S ∈ P.accept_states) (P.start ∪ P.step S b) (P.step S none)) (λ b, P.step S b),
    start := P.start,
    accept_states := P.accept_states }
| (RPlus P Q) := 
  let P := P.ε_NFA_of_regex, Q := Q.ε_NFA_of_regex in
  { state := P.state × Q.state,
    state_fintype := @prod.fintype _ _ P.state_fintype Q.state_fintype,
    step := λ S b, set.prod (P.step S.1 b) (Q.step S.2 b),
    start := set.prod P.start Q.start,
    accept_states := set.prod P.start set.univ ∪ set.prod set.univ Q.start }
| (RComp P Q) := 
  let P := P.ε_NFA_of_regex, Q := Q.ε_NFA_of_regex in
  { state := P.state ⊕ Q.state,
    state_fintype := @sum.fintype _ _ P.state_fintype Q.state_fintype,
    step := λ S b, sum.elim (λ S₁, ite (S₁ ∈ P.accept_states) ((sum.inr '' Q.start) ∪ (sum.inl '' P.step S₁ b)) (sum.inl '' (P.step S₁ b))) (λ S₂, sum.inr '' Q.step S₂ b) S,
    start := sum.inl '' P.start,
    accept_states := sum.inr '' Q.accept_states }

end regex