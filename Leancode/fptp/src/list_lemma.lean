import
  tactic.find tactic.omega 

lemma zip_with_len_l {α β γ : Type*} {l₁ : list α} {l₂ : list β} {f : α → β → γ}
  (h : list.length l₁ = list.length l₂) : 
  list.length (list.zip_with f l₁ l₂) = list.length l₁ :=
begin
  induction l₁ with x xs ih generalizing l₂,
    {simp [list.zip_with]},
    {
      cases l₂ with y ys,
        {injection h},
        {simp only [list.zip_with, list.length], finish}
    }
end

lemma map_with_len_l {α β : Type*} {l₁ : list α} {f : α → β} : 
  list.length (list.map f l₁) = list.length l₁ :=
begin
  induction l₁ with x xs ih, 
  {simp [list.map]}, 
  {simp [list.map]},
end