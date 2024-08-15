/-! Chapter4.lean - Notes and Examples -/

section universal
/- Universal quantification and dependent function types 
  See: [[id:45EC5276-F395-41C0-A0D6-166BDF74EB5E][Introduction and Elimination]]
-/


/- Here another way of stating hypotheses/premises - personally I like to seem
them in place so that the theorem reads well independently although this can be
used tastefull to reduce notational clutter.  -/

-- r is a binary relation
variable (α : Type) (r : α → α → Prop)
-- r is reflexive
variable (refl_r : ∀ x, r x x)
-- r is symmetric
variable (symm_r : ∀ {x y}, r x y → r y x)
-- r is transitive
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)
-- and thus an equivalence relation
example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

/- Nota: impredicativity of Prop 
   -----------------------------
   It is the typing rule for dependent arrow types, and the universal quantifier
   in particular, that distinguishes Prop from other types. Suppose we have α :
   Sort i and β : Sort j, where the expression β may depend on a variable x :
   α. Then (x : α) → β is an element of Sort (imax i j), where imax i j is the
   maximum of i and j if j is not 0, and 0 otherwise.  -/
end universal

/- Equality - is an equivalence relation -/
section equality
#check Eq.refl
#check Eq.symm
#check Eq.trans

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

/- notation for Eq.refl _ -/

example (f : α → β) (a : α) : (λ x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

/- every eq assertion respects the equivalence -/

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

#check Eq.rec
#check Eq.subst


/- calculation based proofs -/
section calculation

variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T₁ : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4


example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

/- You can "teach" calc new transitivity theorems by adding new instances of the
Trans type class. Type classes are introduced later, but the following small
example demonstrates how to extend the calc notation using new Trans instances.
-/

def divides (x y : Nat) : Prop := ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

infix:50 "|" => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x | y   := h₁
    _ = z   := h₂
    _ | 2*z := divides_mul ..

end calculation
end equality

section existential

#check Exists.intro
#check Exists.elim

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro -- ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p

-- Exists.elim
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

-- eliminate Exists with match
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

-- for greater clarity annotate the types
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

-- the conjunction can be matched at the same time
variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

-- pattern matching let
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

-- implicit match with abstraction
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  λ ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

-- basic number theory I think we just met up with mathematics in lean or
-- mechanics of proof...

def is_even (a : Nat) := ∃ b, a = 2 * b

-- golf in progress...
theorem even_plus_even₁ (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))

-- or more concisely with context driven constructor pattern matching
theorem even_plus_even₂ (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

-- let's be really concise  
theorem even_plus_even : is_even a ∧ is_even b → is_even (a + b) :=
  λ ⟨⟨w1, hw1⟩, ⟨w2, hw2⟩⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩


/- Just as the constructive "or" is stronger than the classical "or," so, too,
   is the constructive "exists" stronger than the classical "exists". For example,
   the following implication requires classical reasoning because, from a
   constructive standpoint, knowing that it is not the case that every x satisfies
   ¬p is not the same as having a particular x that satisfies p.  -/

open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)

end existential

