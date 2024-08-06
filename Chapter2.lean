

/- Nota: some syntax disagreements with , in place of the => 
   this was due to reading the lean3 documentation in error! -/

def dotwice : (Nat → Nat) → Nat → Nat := λ f x ↦ f (f x)

#check dotwice

/- infix section -/
#check (. + 1)

#eval dotwice (. + 2) 5


def add (x y : Nat) : Nat := 
  x + y

#check (add 2)

#eval dotwice (add 2) 5

/- Lean doesn't know what ℕ is at this point! - (prolly need mathlib) so by using
  this notation as a type var (default Sort u_1) confused me for while as it is
  equivalent (isomorphic) to this function: -/

def dotwain : (A → A) → A → A := λ f x ↦ f (f x)

section myuniverse
  /- I guess we could make it polymorphic in the universe u -/
  universe u


  def dotwainly {A : Type u} : (A → A) → A → A := λ f x ↦ f (f x)
  #check dotwainly

end myuniverse -- ooh

/- or more succintly if less comprehensible -/

def do2.{u} (A : Type u) : (A → A) → A → A := λ f x ↦ f (f x)
#check do2

/- universe poolymorphic identity -/
def ident.{u} {α : Type u} (x : α) := x

#check ident

#eval ident 42
#eval ident "forty two"

#check @ident
