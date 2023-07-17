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
    
/-- A random element with a given property from a list. As IO may in principle give an error, we specify a default to fallback and the conditions that this is in the list and has the property `p` - Code that we borrowed from Professor Gadgil  -/
def pickElemD [DecidableEq α](l: List α)(p: α → Bool)(default : α)(h₁ : default ∈ l)(h₂ : p default = true)
  : 
    {t : α // t ∈ l ∧ p t = true} := (pickElemIO l p ⟨default, h₁, h₂⟩).run' () |>.getD ⟨default, h₁, h₂⟩

/--First Filter which filters out all non-Charmichael Numbers -/
def first_filter (l : List ℕ): List ℕ  := 
  match l with 
  | []  =>  []
  | head :: tail => 
    if (2^(head) % head) = 2 % head then
      head :: first_filter tail
    else
      first_filter tail


/--Theorem which asserts the fact that removing 0 from a list makes the list zeroless-/
theorem remove_zero (l : List ℕ) : 0 ∉ List.remove 0 l := by 
  intro contra 
  rw[List.mem_remove_iff] at contra
  apply contra.2
  simp only



/--Merge Sort algorithm to get them in ascending order -/
def merge_sort(l : List ℕ) : List ℕ := 
  List.mergeSort LE.le l

/--Function to show if the list is non-empty or not -/
def non_empty(l : List ℕ) : Bool := 
  match l with 
  | [] => 
  panic! "list is empty" 
  | head :: tail => true

/--Generates the Proof that the list is non-empty-/
theorem non_empty_list (l : List ℕ )(h : non_empty l = true) : l ≠ [] := by 
  match l with 
  | [] => 
    contradiction
  | head :: tail => 
    simp only [non_empty] at h
    intro contra
    contradiction

  
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

/--Inverse of the divides_auxilary function-/
theorem divides_aux_inv (n : ℕ)(l : List ℕ)(lem : ∀ m ∈ l, ¬m ∣ n) : divides l n = false := by 
  match l with 
  | [] => 
    simp only [divides]
  | head :: tail => 
    simp only [divides, Bool.ite_eq_false_distrib, if_false_left_eq_and]
    apply And.intro
    · intro contra
      rw[← Nat.dvd_iff_mod_eq_zero] at contra
      exact lem head (List.mem_cons_self head tail) contra
    · have lem' : ∀ m ∈ tail, ¬m ∣ n := by 
        intro m h₀ h₁
        exact lem m (List.mem_cons_of_mem head h₀) h₁
      exact divides_aux_inv n tail lem'

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

 /--inverse of the divides_equiv theorem-/ 
theorem divides_equiv_inv(n : ℕ)(hn : n ≥ 4)(lem : ∀ (m : ℕ), 2 ≤ m → m ≤ Nat.sqrt n → ¬m ∣ n) : divides (List.range' 2 ((Nat.sqrt n) - 1)) n = false := by
  apply divides_aux_inv n (List.range' 2 ((Nat.sqrt n) - 1))
  intro m h₀ h₁ 
  rw[List.mem_range'] at h₀
  have obv : 2 + (Nat.sqrt n - 1) = Nat.sqrt n + 1 := by
    have h₃ : 1 ≤  Nat.sqrt n  := by 
      rw[Nat.le_sqrt'] 
      linarith 
    have h₄ : 2 = 1 + 1 := by norm_num
    rw[h₄,add_assoc]
    have h₅ : 1 + (Nat.sqrt n -1) = Nat.sqrt n := by 
      apply Nat.add_sub_cancel' h₃ 
    rw[h₅]
    linarith only [h₁]   
  rw[obv] at h₀
  have h3 : m ≤  Nat.sqrt n  := by 
    linarith only [h₀.2]
  exact lem m h₀.1 h3 h₁

  
/--Nat.Prime Generator Function Auxilary-/
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

/--Inverse of the above theorem -/
theorem is_prime_gen (n : ℕ)(hn : Nat.Prime n) : (is_prime n) = true := by 
  rw[is_prime]
  split_ifs
  · rename_i  h 
    have h' : n = 0 ∨ n = 1 := by 
      interval_cases n
      all_goals {simp}
    cases h' with 
    | inl h₁ => 
      rw[h₁] at hn
      exact Nat.not_prime_zero hn
    | inr h₁ => 
      rw[h₁] at hn
      exact Nat.not_prime_one hn 
  · rename_i h₁ h₂  
    simp
  · rename_i h₁ h₂  
    simp 
    rw[Nat.not_lt_eq] at h₂
    apply divides_equiv_inv n h₂ 
    rw[Nat.prime_def_le_sqrt] at hn
    exact hn.2


/--outputs minimum Prime in an ordered list-/
def min_prime_list? (l : List ℕ) : Option { p : Nat // Nat.Prime p ∧ p ∈ l}:=
  match l with 
  | [] => none
  | head :: tail => 
    if c : is_prime head then
      some ⟨head,prime_gen head c, by simp only [List.find?, List.mem_cons, true_or]⟩
    else
      do 
        let ⟨p,hp, hl⟩ ← min_prime_list? tail
        some ⟨p,hp, by simp only [List.find?, List.mem_cons, hl, or_true]⟩
        

-- def hmain_generation (l : List ℕ)(h : l ≠ [])(h0 : 0 ∉ l) : Bool :=
--   if min_prime_list l ≠ 0 then
--     true
--   else
--     panic! "list has no prime element"

-- /--Hmain generation function -/
-- theorem hmain_generation_theorem (l : List ℕ)(h : l ≠ [])(h0 : 0 ∉ l) : hmain_generation l h h0 = true →  min_prime_list l ≠ 0 := by
--   intro hmain contra
--   rw[hmain_generation] at hmain
--   simp at hmain
--   exact hmain contra


def gen_prime_pair?(l : List Nat) : Option (Subtype $ fun (p,q) ↦ Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q) := do
  let ⟨ p,hp,_⟩  ← min_prime_list? l
  let ⟨q , hq, hql⟩ ← min_prime_list? (List.remove p l)
  return ⟨(p,q),⟨hp , hq , Ne.symm (List.mem_remove_iff.mp hql).right  ⟩⟩


def permuteList(l : List ℕ) : IO (List ℕ) := do
  match l with 
  | [] => return []
  | a :: [] => return [a]
  | a :: b :: tail => 
    let r ← IO.rand 0 1
    if r = 0 then
      let l' ← permuteList (b :: tail)
      return (a :: l')
    else
      let l' ← permuteList (a :: tail)
      return (b :: l') 


/--Coprime Checking Function-/
def is_coprime (a : ℕ)(b: ℕ) : Bool :=
  if Nat.gcd a b = 1 then
    true
  else
    false

/-- Theorem which generates that gcd a m = 1-/
theorem coprime_generator (a : ℕ)(b : ℕ)(h : is_coprime a b = true) : Nat.coprime a b := by 
  simp [is_coprime] at h
  exact of_not_not (mt h not_false) 


def gen_coprime_pair?(l : List ℕ)(a : ℕ) : Option { p : Nat // Nat.coprime a p ∧ p ∈ l}:=
  match l with 
  | [] => none
  | head :: tail => 
    if c : is_coprime a head then
      some ⟨head,coprime_generator a head c, by simp only [List.find?, List.mem_cons, true_or]⟩
    else
      do 
        let ⟨p,hp, hl⟩ ← gen_coprime_pair? tail a
        some ⟨p,hp, by simp only [List.find?, List.mem_cons, hl, or_true]⟩


-- /-- Defines an eligible List-/
-- structure Eligible_List where 
--   l : List ℕ
--   h : l ≠ []
--   h0 : 0 ∉ l
--   hmain : min_prime_list l ≠ 0
--   deriving Repr

-- /--Eligible List Generator-/
-- def Eligible_List_generator(l : List ℕ) : Eligible_List:=
--   let l1 := first_filter l
--   let l2 := List.remove 0 l1
--   let h0 := remove_zero l2
--   sorry
   
  

-- /--Theorem to check if no prime exists in l-/
-- theorem prime_in_list (l : List ℕ)(h : l ≠ [])(h0 : 0 ∉ l): min_prime_list l ≠  0 ↔ ∃ m ∈ l, Nat.Prime m := by
--   apply Iff.intro 
--   · intro contra
--     match l with 
--     | [] => 
--       contradiction
--     | head :: tail =>
--       rw[min_prime_list] at contra
--       split_ifs at contra
--       · rename_i h' 
--         use head 
--         apply And.intro
--         · simp
--         · exact prime_gen head h' 
--       · rename_i h'
--         have lem (hr :∃ m, m ∈ head :: tail ∧ Nat.Prime m ) : ∃ m , m ∈ tail ∧ Nat.Prime m := by 
--           cases hr with 
--           | intro m hm => 
--             use m 
--             have h2 : ¬(Nat.Prime head) := by 
--               intro contra'
--               apply h' 
--               exact is_prime_gen head contra'
--             have h1 : m ≠head := by 
--               intro contra'
--               rw[← contra'] at h2
--               exact h2 hm.2
--             apply And.intro
--             · simp [h1] at hm 
--               exact hm.1
--             · exact hm.2  
--         sorry
           
--   · sorry  

-- /--Produces the proof that the minimum prime is in the list-/
-- theorem min_prime_list_in_list (l : List ℕ)(h : l ≠ []) (h0 : 0 ∉ l )(hmain : min_prime_list l ≠ 0) : min_prime_list l ∈ l := by
--   match l with 
--   | [] => 
--     contradiction
--   | head :: tail =>
--     rw[min_prime_list] at hmain
--     split_ifs at hmain
--     · rename_i h' 
--       rw[min_prime_list]
--       simp [h']
--     · rename_i h'  
--       rw[min_prime_list]
--       simp [h']
--       have lem : tail ≠ [] := by 
--         by_contra contra
--         rw[contra] at hmain
--         rw[min_prime_list] at hmain
--         apply hmain
--         simp
--       have lem2 : 0 ∉ tail := by
--         intro contra
--         apply h0
--         simp [contra]
--       right 
--       apply min_prime_list_in_list tail lem lem2 hmain

-- /--Produces the proof that the minimum prime is prime-/
-- theorem min_prime_list_is_prime (l : List ℕ)(h : l ≠ []) (h0 : 0 ∉ l )(hmain : min_prime_list l ≠ 0) : is_prime (min_prime_list l) := by
--   match l with 
--   | [] => 
--     contradiction
--   | head :: tail =>
--     rw[min_prime_list] at hmain
--     split_ifs at hmain
--     · rename_i h' 
--       rw[min_prime_list]
--       simp [h']
--     · rename_i h'  
--       rw[min_prime_list]
--       simp [h']   
--       have lem : tail ≠ [] := by 
--         by_contra contra
--         rw[contra] at hmain
--         rw[min_prime_list] at hmain
--         apply hmain
--         simp
--       have lem2 : 0 ∉ tail := by
--         intro contra
--         apply h0
--         simp [contra]
--       simp[min_prime_list_is_prime tail lem lem2 hmain]



-- structure Eligible_List' where 
--   l : List ℕ
--   h : l ≠ []
--   h0 : 0 ∉ l
--   hmain : min_prime_list l ≠ 0
--   deriving Repr

-- /-- Auxilary Function to RandomPrimeGenerator fumction -/
-- def RandomPrimeGenerator_aux(el : Eligible_List) : { t : ℕ // t ∈ el.l ∧ is_prime t = true} := 
--   pickElemD el.l is_prime (min_prime_list el.l) (min_prime_list_in_list el.l el.h el.h0 el.hmain) (min_prime_list_is_prime el.l el.h el.h0 el.hmain)

-- /-- Picking Out a random Prime from a list of natural numbers which also outputs the fact that the number is Prime -/
-- def RandomPrimeGenerator(el : Eligible_List) : { t : ℕ // t ∈ el.l ∧ Nat.Prime t} := 
--   let a := RandomPrimeGenerator_aux el
--   ⟨a.val, ⟨ a.property.1, prime_gen (a.val) (a.property.2)⟩ ⟩

-- /--n + 1 is coprime to n + 2 -/
-- theorem coprime (n : ℕ)(lem :n ≥ 2) : is_coprime (n + 1) (n + 2) = true := by 
--   simp [is_coprime]
--   intro contra
--   have lem : Nat.gcd (n + 1) (n + 2) = 1 := by
--     rw[← Nat.succ_eq_add_one]
--     rw[Nat.gcd_succ n (n + 2)]
--     rw[Nat.succ_eq_add_one]
--     have h' : 2 = 1 + 1 := by ring
--     rw[h',← add_assoc]
--     set b := n + 1 with h 
--     have h1 : (b + 1)% b = 1 := by 
--       rw[Nat.add_mod]
--       rw[Nat.mod_self]
--       ring_nf
--       rw[Nat.mod_mod]
--       set b' := n - 1 with h''
--       have h3 : n ≠ 0 := by 
--         intro contra'
--         rw[contra'] at lem
--         have : ¬(0 ≥ 2) := by ring_nf
--         exact this lem
--       have h2 : b' + 1 = n := by 
--         rw[h'']
--         exact Nat.succ_pred h3 
--       rw[h2.symm]
--       have : 1 + (b' + 1) = b' + 2 := by ring
--       rw[this]
--       exact Nat.one_mod b'
--     rw[h1]
--     simp
--   exact contra lem
-- /-- More Condensed Form of the above theorem-/
-- theorem coprime' (n : ℕ)(hn : n ≥ 1) : is_coprime n (n + 1) = true :=by 
--   sorry
-- /--Theorem which states that the co-prime number was in the desired list-/
-- theorem co_prime_in_list (n : ℕ)(hn: n ≥ 4 ) : n - 1 ∈ List.range' 3 (n - 3):=by 
--   set b := n - 3 with hb 
--   have hb1 : b ≥ 1 := by 
--     rw[hb]
--     exact Nat.sub_le_sub_right hn 3
--   have :  b - 1 = n - 4 := by  sorry 
--   have h : n - 1 = 3 + (n - 4) := by sorry
--   sorry

-- /--Random Co-prime generator -/
-- def RandomCoPrimeGenerator_aux (n : ℕ)(hn : n ≥ 4) : {t : ℕ // t ∈ List.range' 3 (n - 3) ∧ is_coprime n t = true} := 
--   pickElemD (List.range' 3 (n - 3)) (is_coprime n) (n-1) (co_prime_in_list n hn) (coprime' n hn)

-- /-!
-- ## Random Monad

-- We used the IO Monad which has a lot of stuff besides randomness.-/