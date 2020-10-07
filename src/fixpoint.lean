import data.set.lattice

inductive least_fixpoint {α : Type} (f : set α → set α) : set α → α → Prop
| base : ∀ s (x ∈ s), least_fixpoint s x
| step : ∀ s x (h : least_fixpoint s x), least_fixpoint (f s) x

namespace least_fixpoint

lemma fixpoint_of_fixpoint {α : Type} (f : set α → set α) (h : ∀ s, s ⊆ f s) : 
  ∀ s : set α, least_fixpoint f (least_fixpoint f s) = least_fixpoint f s :=
begin
  intro s,
  ext x,
  split,
  { intro h,
    induction h with _ _ _ t y h ih,
    { tauto },
    { tauto } },
  { exact least_fixpoint.base _ _ }
end

lemma fixpoint_of_subset {α : Type} (f : set α → set α) (h : ∀ s, s ⊆ f s) (s t : set α) (hst : s ⊆ t) :
  ∀ x, least_fixpoint f s x → least_fixpoint f t x :=
begin
  intros x hs,
  induction hs with _ _ _ _ _ _ ih,
  { apply least_fixpoint.base,
    tauto },
  { apply ih,
    tauto }
end

lemma fixpoint_of_Union_of_fixpoint {α β : Type} (f : set α → set α) (h : ∀ s, s ⊆ f s) (g : β → set α) :
  ∀ x, x ∈ (⋃ (i : β), least_fixpoint f (g i)) → least_fixpoint f (⋃ (i : β), g i) x :=
begin
  intro x,
  rintro ⟨ s, ⟨ i, hi ⟩, hs ⟩,
  rw ←hi at hs,
  change least_fixpoint f (g i) x at hs,
  generalize_hyp ht : (g i) = t at hs,
  induction hs with _ _ _ _ _ hs,
  { apply least_fixpoint.base,
    finish },
  { apply fixpoint_of_subset _ h _ _ _ _ hs,
    finish }
end

end least_fixpoint