import Mathlib
/-!
# Random sampling for an element

We implement sampling to find an element with a given property, for instance being prime or being coprime to a given number. For this we need a hypothesis that such an element exists. 

We use the `IO` monad to generate random numbers. This is because a random number is not a function, in the sense of having value determined by arguments.
-/

/-!
The basic way we sample is to choose an element at random from the list, and then check if it satisfies the property. If it does, we return it. If not, we remove it from the list and try again. To show termination we see (following a lab) that the length of the list decreases by at least one each time.
-/

universe u
/-- Removing an element from a list does not increase length -/
theorem remove_length_le {α :  Type u} [DecidableEq α](a : α) (l : List α) : (List.remove a l).length ≤ l.length := by 
  induction l with
  | nil => 
    simp [List.remove]
  | cons h' t ih => 
      simp [List.remove]
      split
      · apply Nat.le_step
        assumption
      · rw [List.length_cons]
        apply Nat.succ_le_succ
        exact ih


/-- Removing a member from a list shortens the list -/
theorem remove_mem_length  {α :  Type u} [DecidableEq α]{a : α } {l : List α} (hyp : a ∈ l) : (List.remove a l).length < l.length  := by 
  induction l with
  | nil => 
    contradiction
  | cons h' t ih => 
      simp [List.remove]
      split 
      · apply Nat.lt_succ_of_le
        apply remove_length_le
      · rw [List.length_cons]
        apply Nat.succ_lt_succ
        have in_tail: a ∈ t := by 
          have : ¬ a = h' := by assumption
          simp [List.mem_cons, this] at hyp
          assumption
        exact ih in_tail


/-!
We pick an index of the list `l`, which is of type `Fin l.length`. Rather than proving that the random number generator has this property we pass `mod n`.
-/

/-- A random number in `Fin n` -/
def IO.randFin (n : ℕ)(h : 0 < n ) : IO <| Fin n   := do
  let r ← IO.rand 0 (n - 1)
  pure ⟨r % n, Nat.mod_lt r h⟩


/-- A random element with a given property from a list, within `IO`  -/
def pickElemIO [DecidableEq α](l: List α)(p: α → Bool)(h : ∃t : α, t ∈ l ∧ p t = true) : IO {t : α // t ∈ l ∧ p t = true} := do
  have h' : 0 < l.length := by 
    have ⟨t, h₀⟩ := h
    apply List.length_pos_of_mem h₀.left
  let index ← IO.randFin l.length h' 
  let a := l.get index
  if c:p a = true then
    return ⟨a, by 
      simp [c]
      apply List.get_mem
      ⟩
  else
    let l' := l.remove a
    have h' : ∃t : α, t ∈ l' ∧ p t = true :=
      by
        have ⟨t, h₁, h₂⟩ := h
        use t
        simp [List.mem_remove_iff, h₁, h₂]
        simp at c
        intro contra
        simp [contra, c] at h₂
    have : l'.length < l.length := by
      apply remove_mem_length
      apply List.get_mem
    let ⟨t, h₁, h₂⟩ ←  pickElemIO l' p h'
    have m : t ∈ l := 
      List.mem_of_mem_remove h₁
    return ⟨t, m, h₂⟩
termination_by _ _ _ l _ _ => l.length  
    
/-- A random element with a given property from a list. As IO may in principle give an error, we specify a default to fallback and the conditions that this is in the list and has the property `p` -/
def pickElemD [DecidableEq α](l: List α)(p: α → Bool)(default : α)(h₁ : default ∈ l)(h₂ : p default = true)
  : 
    {t : α // t ∈ l ∧ p t = true} := (pickElemIO l p ⟨default, h₁, h₂⟩).run' () |>.getD ⟨default, h₁, h₂⟩

/--First Filter -/
def first_filter (l : List ℕ): List ℕ  := 
  match l with 
  | []  =>  []
  | head :: tail => 
    if (2^(head) % head) = 2 % head then
      head :: first_filter tail
    else
      first_filter tail

/--Division Checker -/
def divides (l : List ℕ)(c : ℕ) : Bool := 
  match l with
  | [] => false
  | head :: tail => 
    if c % head = 0 then
      true
    else
      divides tail c

/--Prime Checking Function-/
def is_prime (n : ℕ) : Bool :=  
  if n < 2 then
    false
  else
    if n < 4 then
      true
    else
      let l := List.range' 2 ((Nat.sqrt n) - 1) 
      not (divides l n)

/--divides function auxilary-/
theorem divides_aux (n : ℕ)(l : List ℕ)(lem : divides l n = false) : ∀ m ∈ l, ¬m ∣ n := by 
  intros m h₀ h₁
  match l with 
  | [] => 
    contradiction
  | head :: tail =>
    simp [divides] at lem
    cases h₀ 
    · rw[Nat.dvd_iff_mod_eq_zero] at h₁
      exact lem.1 h₁ 
    · rename_i h 
      exact divides_aux n tail lem.2 m h h₁

/--divides function equivalence-/
theorem divides_equiv (n : ℕ)(lem : divides (List.range' 2 ((Nat.sqrt n) - 1)) n = false) : ∀ (m : ℕ), 2 ≤ m → m ≤ Nat.sqrt n → ¬m ∣ n := by  
  intros m h₀ h₁ h₂
  have h : m ∈ List.range' 2 ((Nat.sqrt n) - 1) := by 
    rw[List.mem_range']
    apply And.intro
    · assumption
    · have h₃ : 1 ≤  Nat.sqrt n  := by 
        linarith only [h₀,h₁]
      have h₄ : 2 = 1 + 1 := by norm_num
      rw[h₄,add_assoc]
      have h₅ : 1 + (Nat.sqrt n -1) = Nat.sqrt n := by 
        apply Nat.add_sub_cancel' h₃ 
      rw[h₅]
      linarith only [h₁] 
  exact divides_aux n (List.range' 2 ((Nat.sqrt n) - 1)) lem m h h₂

lemma prime_gen_aux (n : ℕ)(hn1 : 2 ≤ n)(hn2 : n < 4)  : n = 2 ∨ n = 3 := by
  interval_cases n
  all_goals {simp}

/-- Nat.Prime Generator Function-/
theorem prime_gen (n : ℕ)(hp : (is_prime n) = true) : Nat.Prime n := by 
  rw[is_prime] at hp
  simp at hp
  by_cases h : 4 ≤ n 
  · rw[Nat.prime_def_le_sqrt]
    apply And.intro 
    · exact hp.1
    · exact divides_equiv n (hp.2 h) 
  · have h' : n < 4 := by 
      linarith only [h]
    have h'' : n = 2 ∨ n = 3 := by 
      exact prime_gen_aux n (hp.1) h'
    cases h''
    · rename_i h₁
      rw[h₁]
      exact Nat.prime_two
    · rename_i h₁
      rw[h₁]
      exact Nat.prime_three
    
/--outputs minimum Prime in a list-/
def min_prime_list (l : List ℕ) : ℕ :=
  match l with 
  | [] => 0
  | head :: tail => 
    if is_prime head then
      head
    else
      min_prime_list tail 



/--Produces the proof that the minimum prime is in the list-/
theorem min_prime_list_in_list (l : List ℕ)(h : l ≠ []) (h0 : 0 ∉ l )(hmain : min_prime_list l ≠ 0) : min_prime_list l ∈ l := by
  match l with 
  | [] => 
    contradiction
  | head :: tail =>
    rw[min_prime_list] at hmain
    split_ifs at hmain
    · rename_i h' 
      rw[min_prime_list]
      simp [h']
    · rename_i h'  
      rw[min_prime_list]
      simp [h']
      have lem : tail ≠ [] := by 
        by_contra contra
        rw[contra] at hmain
        rw[min_prime_list] at hmain
        apply hmain
        simp
      have lem2 : 0 ∉ tail := by
        intro contra
        apply h0
        simp [contra]
      right 
      apply min_prime_list_in_list tail lem lem2 hmain

/--Produces the proof that the minimum prime is prime-/
theorem min_prime_list_is_prime (l : List ℕ)(h : l ≠ []) (h0 : 0 ∉ l )(hmain : min_prime_list l ≠ 0) : is_prime (min_prime_list l) := by
  match l with 
  | [] => 
    contradiction
  | head :: tail =>
    rw[min_prime_list] at hmain
    split_ifs at hmain
    · rename_i h' 
      rw[min_prime_list]
      simp [h']
    · rename_i h'  
      rw[min_prime_list]
      simp [h']   
      have lem : tail ≠ [] := by 
        by_contra contra
        rw[contra] at hmain
        rw[min_prime_list] at hmain
        apply hmain
        simp
      have lem2 : 0 ∉ tail := by
        intro contra
        apply h0
        simp [contra]
      simp[min_prime_list_is_prime tail lem lem2 hmain]

/-- Defines an eligible List-/
structure Eligible_List where 
  l : List ℕ
  h : l ≠ []
  h0 : 0 ∉ l
  hmain : min_prime_list l ≠ 0
  deriving Repr

/-- Picking Out a random Prime from a list of natural numbers -/
def RandomPrimeGenerator_aux(el : Eligible_List) : { t : ℕ // t ∈ el.l ∧ is_prime t = true} := 
  pickElemD el.l is_prime (min_prime_list el.l) (min_prime_list_in_list el.l el.h el.h0 el.hmain) (min_prime_list_is_prime el.l el.h el.h0 el.hmain)

/-- -/ 
def RandomPrimeGenerator(el : Eligible_List) : { t : ℕ // t ∈ el.l ∧ Nat.Prime t} := 
  let a := RandomPrimeGenerator_aux el
  ⟨a.val, ⟨ a.property.1, prime_gen (a.val) (a.property.2)⟩ ⟩


/-!
## Random Monad

We used the IO Monad which has a lot of stuff besides randomness.-/
