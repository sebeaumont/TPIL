section exercises

/- these are the exercise (solutions) from chapter 4 -/
def even (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

def divides (n m : Nat) : Prop :=
  ∃ k, k * n = m

def prime (n : Nat) : Prop :=
  ¬∃ k : Nat, divides k n ∧ (k > 1) ∧ ¬(k = n)

example (h: prime 7) : Prop := sorry
    
  
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r :=
  λ ⟨_, hr⟩ => hr

example (a : α) : r → (∃ _ : α, r) :=
  λ h : r => ⟨a, h⟩ -- Exists.intro

example : (∃ x, p x ∧ r) → (∃ x, p x) ∧ r :=
  λ ⟨hx, ⟨hp, hr⟩⟩ => ⟨⟨hx, hp⟩, hr⟩

#check Exists.elim

/- The quantifer (∃) can distribute over the disjunction. -/
example : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x) :=
  λ ⟨w, hw⟩ =>
    Or.elim hw
      (λ hp : p w =>
        Or.inl ⟨w, hp⟩)
      (λ hq : q w =>
        Or.inr ⟨w, hq⟩)


example : (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x) :=
  (λ h : (∃ x, p x) ∨ (∃ x, q x) =>
    Or.elim h
      (λ ⟨w, hpw⟩ =>
        ⟨w, Or.inl hpw⟩)
      (λ ⟨w, hqw⟩ =>
        ⟨w, Or.inr hqw⟩))


/- Analagous with de-morgan's laws -/

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (λ h: (¬ ∃ x, p x) =>
      λ x : α =>
        λ hx : p x =>
          h ⟨x, hx⟩)
    (λ h: (∀ x, ¬ p x) =>
      λ h2: (∃ x, p x) =>
        let ⟨w, hw⟩ := h2
        (h w) hw)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (λ h : (∀ x, p x → r) =>
      λ h2 : (∃ x, p x) =>
        let ⟨w, hw⟩ := h2
        (h w) hw)
    (λ h : (∃ x, p x) → r =>
      λ w : α =>
        λ hw : p w =>
          h ⟨w, hw⟩)

/- classical reasoning required for following proofs -/
section classical
open Classical

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun h : (∃ x, r → p x) =>
      fun hr : r =>
        let ⟨w, hw⟩ := h
        ⟨w, hw hr⟩ )
    (fun h : (r → ∃ x, p x) =>
      byCases
        (fun hr : r =>
          let ⟨w, hw⟩ := h hr
          ⟨w, λ _ => hw⟩  )
        (fun hnr : ¬r =>
          ⟨a, fun hr : r =>
            absurd hr hnr⟩ ))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ _ => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h: (∀ x, p x) =>
      fun h2: (∃ x, ¬ p x) =>
        let ⟨w, wh2⟩ := h2
        wh2 (h w))
    (fun h: ¬(∃ x, ¬ p x) =>
      fun z: α =>
        Or.elim (em (p z))
          (fun hpz: p z => hpz)
          (fun hnpz: ¬(p z) => absurd ⟨z, hnpz⟩ h))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h: (∃ x, p x) =>
      let ⟨w, wh⟩ := h
      fun h2: (∀ x, ¬ p x) =>
        (h2 w) wh)
    (fun h: ¬(∀ x, ¬ p x) =>
      byContradiction
        fun h2 : ¬(∃ x, p x) =>
          h fun x : α =>
            fun hx : p x =>
              h2 ⟨x, hx⟩)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h: (¬ ∀ x, p x) =>
      byContradiction
        fun h2 : ¬(∃ x, ¬ p x) =>
          h fun x : α =>
            Or.elim (em (p x))
              (fun hpx : p x => hpx)
              (fun hnpx : ¬(p x) => absurd ⟨x, hnpx⟩ h2))
    (fun h: (∃ x, ¬ p x) =>
      fun h2: (∀ x, p x) =>
        let ⟨w, hw⟩ := h
        hw (h2 w) )

end classical

-- some assertions and conjectures

def infinitely_many_primes : Prop :=
  ∀ n : Nat, ∃ m : Nat, m > n ∧ prime m

def Fermat_prime (n : Nat) : Prop :=
  ∀ k : Nat, n = 2 ^ (2 ^ k) ∧ k > 0

def infinitely_many_Fermat_primes : Prop :=
  ∀ n : Nat, ∃ m : Nat, m > n ∧ Fermat_prime m

-- every number greater than 2 is the sum of two primes
def Goldbach_conjecture : Prop :=
  ∀ n : Nat, n > 2 ∧ ∃ k l : Nat, prime k ∧ prime l ∧ n = l + k

def odd (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k + 1

-- every odd number greater than 5 is the sum of three primes
def Goldbach's_weak_conjecture : Prop :=
  ∀ n : Nat, n > 5 ∧ odd n ∧ ∃ l k m : Nat, prime l ∧ prime k ∧ prime m ∧ n = l + k + m

/- Wikipedia: no three positive integers a, b, and c satisfy the equation a^n +
   b^n = c^n for any integer value of n greater than 2. The cases n = 1 and n = 2
   have been known since antiquity to have infinitely many solutions. -/
def Fermat's_last_theorem : Prop :=
  ∀ n : Nat, n > 2 ∧ ¬∃ a b c : Nat, a^n + b^n = c^n

end exercises
