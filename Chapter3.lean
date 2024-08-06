/-! Examples with Proposition and Proofs -/
section constructive

-- this is really significant that these are implicit arguments
-- otherwise some lemma may need explicit proposition arguments.

variable {p q r : Prop}

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  ⟨ λ h : p ∧ q => show q ∧ p from ⟨h.right, h.left⟩,
    λ h : q ∧ p => show p ∧ q from ⟨h.right, h.left⟩ ⟩

-- Although the show/from is not required here it makes the goal
-- explicit and easier to take a top down approach. 
example : p ∨ q ↔ q ∨ p := 
  ⟨ λ h : p ∨ q => show q ∨ p from 
      Or.elim h (λ hp => Or.inr hp) (λ hq => Or.inl hq), 
    λ h : q ∨ p => show p ∨ q from 
      Or.elim h (λ hq => Or.inr hq) (λ hp => Or.inl hp) ⟩


/- associativity of ∧ the verbose functional programmers way :) I tried to
factor out the left and right lemma but got weird errors due to the proposition
variables not being decalred as implicit! One to watch for. -/
 
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨ λ h : (p ∧ q) ∧ r => 
      ⟨(And.left ∘ And.left) h, ⟨(And.right ∘ And.left) h, And.right h⟩⟩ , 
    λ h : p ∧ (q ∧ r) => 
      ⟨⟨And.left h, (And.left ∘ And.right) h⟩, (And.right ∘ And.right) h⟩⟩

-- make some theorems
theorem and_assoc_left (h : (p ∧ q) ∧ r) : p ∧ (q ∧ r) :=
  ⟨(And.left ∘ And.left) h, ⟨(And.right ∘ And.left) h, And.right h⟩⟩ 


theorem and_assoc_right (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r :=
  ⟨⟨And.left h, (And.left ∘ And.right) h⟩, (And.right ∘ And.right) h⟩

-- the above example is then
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨ and_assoc_left, and_assoc_right ⟩


/- disjunction or or: 
   the cool `h.elim` method et. al. was the breathrough for me
   first use of good ol' Haskell style `$` paren eliminator :) -/

theorem or_assoc_left (h : (p ∨ q) ∨ r) : p ∨ (q ∨ r) := 
  h.elim
    (λ hpq : p ∨ q =>
      hpq.elim
        (λ hp : p => Or.inl hp)
        (λ hq : q => Or.inr ∘ Or.inl $ hq))
    (λ hr : r => Or.inr ∘ Or.inr $ hr)

theorem or_assoc_right (h : p ∨ (q ∨ r)) : (p ∨ q) ∨ r :=
  h.elim
    (λ hp : p => Or.inl ∘ Or.inl $ hp)
    (λ hqr : q ∨ r =>
      hqr.elim
        (λ hq : q => Or.inl ∘ Or.inr $ hq)
        (λ hr : r => Or.inr hr))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    or_assoc_left 
    or_assoc_right

-- need some more lemma 
theorem and_distr_or_l (h : p ∧ (q ∨ r)) : (p ∧ q) ∨ (p ∧ r) :=
  have hp := h.left
  have hqr := h.right
  hqr.elim
    (λ hq : q => Or.inl ⟨hp, hq⟩)
    (λ hr : r => Or.inr ⟨hp, hr⟩)

-- is this is my proudest proof to date! 
theorem and_distr_or_r (h : (p ∧ q) ∨ (p ∧ r)) : p ∧ (q ∨ r) := 
  h.elim
    (λ hpq : p ∧ q => 
      have hp := hpq.left
      have hq := hpq.right
      ⟨hp, Or.inl hq⟩)
    (λ hpr : p ∧ r =>
      have hp := hpr.left
      have hr := hpr.right
      ⟨hp, Or.inr hr⟩)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  ⟨and_distr_or_l, and_distr_or_r⟩

-- or is it this one!
theorem or_distr_and_l (h : p ∨ (q ∧ r)) : (p ∨ q) ∧ (p ∨ r) :=
  h.elim 
    (λ hp : p => 
      ⟨Or.inl hp, Or.inl hp⟩)
    (λ hqr : q ∧ r => 
      have hq : q := hqr.left
      have hr : r := hqr.right
      ⟨Or.inr hq, Or.inr hr⟩)

theorem or_distr_and_r (h : (p ∨ q) ∧ (p ∨ r)) : p ∨ (q ∧ r) := 
  h.left.elim
    (λ hp : p => Or.inl hp)
    (λ hq : q =>
      -- we can carry on here with the right elim!
      h.right.elim
        (λ hp : p => Or.inl hp)
        (λ hr : r => Or.inr ⟨hq, hr⟩))

-- disjunction distubutes over conjunction
theorem or_distr_and : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  ⟨or_distr_and_l, or_distr_and_r⟩


-- other properties
-- TODO stare at these two for a while...
theorem ll : (p → (q → r)) → (p ∧ q → r) :=
  λ hpqr : p → q → r =>
    λ hpq : p ∧ q => hpqr hpq.left hpq.right

  
theorem lr : (p ∧ q → r) → (p → (q → r)) :=
  λ hpqr : (p ∧ q) → r =>
    λ hp : p =>
      λ hq : q => hpqr ⟨hp, hq⟩

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro ll lr


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨ λ h : (p ∨ q) → r => 
    ⟨ λ hp : p => h (Or.inl hp)
    , λ hq : q => h (Or.inr hq) ⟩ 
  , λ h : (p → r) ∧ (q → r) =>
      λ hpq : p ∨ q =>
        hpq.elim h.left h.right⟩


/- De Morgan's rules -/

theorem not_distr_or_l : ¬(p ∨ q) → ¬p ∧ ¬q := 
  λ h : ¬(p ∨ q) =>
    -- given the hypothesis h we need to construct a
    -- conjunction of not p and not q, since h negates p ∨ q we
    -- can provide a witness (for both p and q) of that
    -- disjunction and produce the p -> False and q -> False
    -- as required.
    ⟨ λ hp : p => h (Or.inl hp),
      λ hq : q => h (Or.inr hq) ⟩

theorem not_distr_or_r : ¬p ∧ ¬q → ¬(p ∨ q) :=
  λ h : ¬p ∧ ¬q =>
    -- given the hypothesis h we need to construct a negation
    -- of the disjunction p OR q, so we provide a function from
    -- p ∨ q -> False; We can prove False in both cases of
    -- the disjunction with the left and right conjunct of h.
    λ hpq : p ∨ q =>
      hpq.elim h.left h.right

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  ⟨ not_distr_or_l, not_distr_or_r ⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  λ h : ¬p ∨ ¬q => 
    -- from the disjunction of ¬p or ¬q we need to show that
    -- the conjunction of p and q is False; from each case 
    -- of the disjunction we can show False as required. 
    λ hpq : p ∧ q =>
      h.elim 
        (λ hnp : ¬p => hnp hpq.left)
        (λ hnq : ¬q => hnq hpq.right)

example : ¬(p ∧ ¬p) :=
  -- we need to show that p ∧ ¬p → False; so apply p → False to p
  -- from the conjuncts to give False as required.
  λ h : p ∧ ¬p => h.right h.left

example : p ∧ ¬q → ¬(p → q) := 
  -- we need to show p → q → False
  λ h : p ∧ ¬q => 
    λ hp : p → q => h.right (hp h.left)

example : ¬p → (p → q) := 
  λ hnp : ¬p => λ hp : p => absurd hp hnp

example : (¬p ∨ q) → (p → q) := 
  λ h : ¬p ∨ q =>
    λ hp : p =>
      h.elim 
        (λ hnp : ¬p => absurd hp hnp)
        id

example : p ∨ False ↔ p := 
  ⟨ λ h : p ∨ False =>
    h.elim
      id
      (λ hf : False => False.elim hf)
  , λ h : p => Or.inl h ⟩

example : p ∧ False ↔ False :=
  ⟨ λ h : p ∧ False => False.elim h.right
  , λ h : False => False.elim h ⟩

-- this is neat
example : (p → q) → (¬q → ¬p) := 
  λ h : p → q =>
    λ hnq : ¬q => 
      -- assume p apply h to p to give q and apply hnq : q -> False
      -- to form p -> False (¬p)
      λ hp : p => hnq (h hp)

/- Q. is EFQ constructive? The only reasonable way to construct
   False is by absurd (contradiction) which is not constructive 
   either AFAIK. See below for this question again. -/

end constructive

-- Here be Dragons! ;-) poor Brouwer would not be happy here...
-- The only dogma is the classical one - History has been
-- revised to suit the loudest voices but right will dominate
-- might in the end.

section classical
open Classical

/- Prove the following identities, replacing the "sorry" placeholders
with actual proofs. These require classical reasoning.  -/ 

-- note these Prop arguments are implicit
variable {p q r : Prop}

-- based on one of other of dne or (l)em we prove the other
-- double negation can be proved using excluded middle
theorem dne (h : ¬¬p) : p :=
  Or.elim (em p)
    (λ hp : p ↦ hp) -- id
    (λ hnp : ¬p ↦ absurd hnp h)

theorem nem (h: ¬(p ∨ ¬p)) : ¬p := 
  λ (hp : p) ↦ h (Or.intro_left (¬p) (hp))

theorem lem : p ∨ ¬p :=
  dne 
    (λ (h : ¬(p ∨ ¬p)) ↦ 
     h (Or.intro_right (p) (nem h)))

-- by cases 
example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

-- by contradiction
example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)

-- TODO make sure you follow/comment these proofs as they are quite 
-- trick.
 
-- em in action 
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ h : p → q ∨ r =>
    -- apply/elimintate excluded middle: p or ¬p 
    --(em p).elim
    Or.elim (em p)
      (λ hp : p =>
        (h hp).elim  -- q ∨ r
          (λ hq : q => Or.inl (λ _ : p => hq))
          (λ hr : r => Or.inr (λ _ : p => hr)))
      (λ hnp : ¬p =>
        Or.inl (λ hp : p => absurd hp hnp))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ h : ¬(p ∧ q) =>
    Or.elim (em p)
      (λ hp : p =>
        Or.elim (em q)
          (λ hq : q => absurd ⟨hp, hq⟩ h )
          (λ hnq : ¬q => Or.inr hnq))
      (λ hnp : ¬p => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  λ h : ¬(p → q) =>
    Or.elim (em q)
      (λ hq : q =>
        absurd (λ _ : p => hq) h)
      (λ hnq : ¬q =>
        Or.elim (em p)
          (λ hp : p => ⟨ hp, hnq ⟩)
          (λ hnp : ¬p =>
            absurd (λ hp : p => absurd hp hnp) h))

example : (p → q) → (¬p ∨ q) :=
  λ h : p → q =>
    Or.elim (em p)
      (λ hp : p => Or.inr (h hp))
      (λ hnp : ¬p => Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  λ h : ¬q → ¬p =>
    Or.elim (em p)
      (λ hp : p =>
        Or.elim (em q)
          (λ hq : q =>
            λ _ : p => hq)
          (λ hnq : ¬q => absurd hp (h hnq)))
      (λ hnp : ¬p =>
        λ hp : p => absurd hp hnp)

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := 
  λ h : (p → q) → p =>
   Or.elim (em p) 
     id
     -- seems odd to have to prove ¬p here
     (λ hnp : ¬p => 
       h (λ hp : p => absurd hp hnp))

end classical

-- weak excluded middle exercise - maybe best left as an apology?
theorem wem {p : Prop} : ¬p ∨ ¬¬p := sorry


section notclassical

/- Of course none of the classical axioms are necessary as we
   can state `dne` as an hypothesis and then prove the theorem
   of the excluded middle: `em` -/

example (dne : {p : Prop} → (¬¬p → p)) : p ∨ ¬p :=
  dne 
    (λ (h : ¬(p ∨ ¬p)) ↦ 
     h (Or.inr (λ hp : p ↦ h (Or.inl hp))))

/- et vice versa state `em` as a hypothesis and prove `dne` -/

example (em : {p : Prop} → p ∨ ¬p) (h: ¬¬p) : p :=
  Or.elim (em)
    id -- (λ hp : p ↦ hp)
    (λ hnp : ¬p ↦ absurd hnp h)
  

-- Prove ¬(p ↔ ¬p) without using classical logic.
/- quite a trick proof!! -/
example : ¬(p ↔ ¬p) :=
  -- we get both directions of the correspondance
  -- hl : p → ¬p, hr : ¬p → p  
  λ ⟨hl, hr⟩ =>
    -- we assume p and prove p → False by hl
    let hp := hr (λ hp : p => (hl hp) hp)
    (hl hp) hp

/- Ex falso sequitur quod libet (EFQ) : we've used this quite a
   bit above but I'm not sure of it's constructive
   credentials... fortunately you can never construct it and be
   sound -/ 
example {p q : Prop} (hp : p) (hnp : ¬p) : q :=
   False.elim (hnp hp)

end notclassical
  

