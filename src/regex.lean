import data.fintype.basic
import data.finset.basic
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

def ε_NFA_of_regex {α : Type u} [fintype α] [h : decidable_eq α] : regex α → ε_NFA α
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
  begin
    let P := P.ε_NFA_of_regex,
    haveI := P.state_dec,
    exact
    { state := P.state,
      state_fintype := P.state_fintype,
      step := λ S b, b.cases_on' (ite (S ∈ P.accept_states) (P.start ∪ (P.step S b)) (P.step S none)) (λ b, P.step S b),
      start := P.start,
      accept_states := P.accept_states }
  end
| (RPlus P Q) := 
  begin
    let P := P.ε_NFA_of_regex,
    let Q := Q.ε_NFA_of_regex,
    haveI := P.state_fintype,
    haveI := Q.state_fintype,
    haveI := P.state_dec,
    haveI := Q.state_dec,
    exact
    { state := P.state × Q.state,
      step := λ S b, finset.product (P.step S.1 b) (Q.step S.2 b),
      start := finset.product P.start Q.start,
      accept_states := finset.product P.start finset.univ ∪ finset.product finset.univ Q.start }
  end
| (RComp P Q) := 
  begin
    let P := P.ε_NFA_of_regex,
    let Q := Q.ε_NFA_of_regex,
    haveI := P.state_fintype,
    haveI := Q.state_fintype,
    haveI := P.state_dec,
    haveI := Q.state_dec,
    exact
    { state := P.state ⊕ Q.state,
      step := λ S b, sum.elim (λ S₁, ite (S₁ ∈ P.accept_states) (finset.image sum.inr Q.start ∪ finset.image sum.inl (P.step S₁ b)) (finset.image sum.inl (P.step S₁ b))) (λ S₂, finset.image sum.inr (Q.step S₂ b)) S,
      start := finset.image sum.inl P.start,
      accept_states := finset.image sum.inr Q.accept_states }
  end

end regex