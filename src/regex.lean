import data.fintype.basic

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

end regex