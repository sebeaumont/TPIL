/- Tactical Leanings -/

theorem test₁ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := 
  ⟨hp, ⟨hq, hp⟩⟩

theorem test₂ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
  
/- take you pick there ;-) -/
