import Mathlib
import RSACryptosystemsI

theorem mod_pow_eq (a : ℕ)(b : ℕ)(n : ℕ)(pos: n ≠ 1)(hneq : n ≠ 0): mod_pow a b n hneq = (a ^ b) % n := by
  unfold mod_pow
  have h1 : n > 1 := by
    have h1' : (n = 0 ∨ n = 1 ∨ n > 1) := by
      cases n
      · simp
      · rename_i k
        simp
        cases k
        · simp
        · rename_i k'
          simp
    cases h1'
    · rename_i left
      rw[left] at pos
      contradiction
    · rename_i right
      cases right
      · rename_i left'
        rw[left'] at pos
        contradiction
      · rename_i right'
        assumption
  split
  · simp     
    rw[Nat.mod_eq_of_lt h1]
  · simp 
  · simp 
    rename_i k
    rw[← Nat.add_one k]
    rw[← Nat.add_one (k / 2)]  
    rw[← Nat.add_one (k + 1)]
    split 
    · rw[mod_pow_eq a (k / 2 + 1) n pos hneq]
      have h : a ^ (k + 1 + 1) = a ^ (k / 2 + 1) * a ^ (k / 2 + 1) := by
        rw[← pow_add]
        have sum : k / 2 + 1 + (k / 2 + 1) = k + 1 + 1 := by
          rw[← add_assoc]
          simp
          rw[add_comm]
          rw[← add_assoc]
          simp 
          rename_i i
          have dvd : 2 ∣ k := by
            apply Nat.dvd_of_mod_eq_zero
            assumption
          have eq : 2 * (k / 2) = k := by
            rw[Nat.mul_div_cancel_left' dvd]
          have twice : k / 2 + k / 2 = 2 * (k / 2) := by
            rw[← Nat.mul_two]
            rw[Nat.mul_comm]
          rw[eq] at twice
          assumption
        rw[sum]
      rw[h]
      generalize a ^ (k / 2 + 1) = b
      rw[← Nat.ModEq]
      have H : (b % n) ≡ b [MOD n] := by
        rw[Nat.ModEq]
        simp
      apply Nat.ModEq.mul H H   
      
    · rw[mod_pow_eq a (k + 1) n pos hneq] 
      have h : a ^ (k + 1 + 1) = a ^ (k + 1) * a:= by
        rw[pow_add]
        simp
      rw[h]
      generalize a ^ (k + 1) = b
      rw[← Nat.ModEq]
      have comm : a * b = b * a := by
        rw[Nat.mul_comm]
      rw[← comm]
      have H : (b % n) ≡ b [MOD n] := by
        rw[Nat.ModEq]
        simp
      apply Nat.ModEq.mul_left a H
termination_by _ _ => b
decreasing_by
sorry


theorem freshman's_dream (a b : ℕ) (hp : Nat.Prime p) : ((a + b) ^ p) % p = (a ^ p + b ^ p) % p := by
  rw[← Nat.ModEq]
  rw[add_pow]
  rw[Nat.ModEq.comm]
  have h1 : {0, p} ⊆ Finset.range (p + 1) := by 
    rw[Finset.subset_iff]
    simp 
  rw[←Finset.sum_sdiff h1]
  have h2 : 0 ≠ p := by 
    intro h3 
    apply Nat.Prime.ne_zero hp
    rw[h3] 
  rw[Finset.sum_pair h2] 
  simp
  rw[Nat.add_comm (a ^ p) (b ^ p)]
  nth_rewrite 1[← Nat.add_zero (b ^ p + a ^ p)] 
  rw[Nat.add_comm] 
  apply Nat.ModEq.add_right 
  apply Nat.ModEq.symm 
  rw[Nat.modEq_zero_iff_dvd]
  apply Finset.dvd_sum 
  intro i hi 
  rw[← Nat.modEq_zero_iff_dvd] 
  have h3 : Nat.choose p i ≡ 0 [MOD p]:= by
    rw[Nat.modEq_zero_iff_dvd] 
    apply Nat.Prime.dvd_choose_self hp
    intro h4
    rw[h4] at hi 
    simp at hi 
    simp[Finset.range] at hi 
    cases hi
    rename_i left right 
    cases left 
    · rename_i left'
      rw[left'] at right
      simp at right
    · rename_i right' 
      assumption
  apply Nat.ModEq.mul_left (a ^ i * b ^ (p - i)) h3

theorem fermat_little_theorem' (p : ℕ) (hp : Nat.Prime p) (a : ℕ) : a ^ p ≡ a [MOD p] := by
  induction a 
  · simp 
    have h1 : 0 ^ p = 0 := by
      simp
      apply Nat.Prime.pos hp
    simp[h1]
    trivial 
  · rename_i k base
    rw[← Nat.add_one k]
    have h1 : (k + 1) ^ p ≡ k ^ p + 1 ^ p [MOD p] := by
      apply freshman's_dream
      assumption
    have h2 : k ^ p + 1 ^ p ≡ k ^ p + 1 [MOD p] := by
      simp
      trivial 
    have h3 : (k + 1) ^ p ≡ k ^ p + 1 [MOD p] := by
      apply Nat.ModEq.trans h1 h2
    have h4 : k ^ p + 1 ≡ k + 1 [MOD p] := by
       apply Nat.ModEq.add_right _ base
    apply Nat.ModEq.trans h3 h4  

  theorem fermat_little_theorem (p : ℕ) (hp : Nat.Prime p) (a : ℕ)(hpneqn : ¬(p ∣ a)) : a ^ (p - 1) % p = 1 := by
  rw[← Nat.Prime.coprime_iff_not_dvd hp] at hpneqn
  rw[Nat.coprime_iff_gcd_eq_one] at hpneqn
  have h1 : a ^ p ≡ a [MOD p] := fermat_little_theorem' p hp a
  have lem : a * a ^ (p - 1) ≡ a * 1 [MOD p] := by
    have h' : a = a * 1 := by
      simp
    rw[← h']
    have h'' : a ^ p = a * a ^ (p - 1) := by
      have h''' : p - 1 + 1 = p := by
        apply Nat.sub_add_cancel hp.pos
      rw[add_comm] at h'''
      nth_rewrite 1[← h'''] 
      rw[pow_add]
      simp
    rw[← h'']
    assumption  
  have h3 : a ^ (p - 1) ≡ 1 [MOD p] := Nat.ModEq.cancel_left_of_coprime hpneqn lem
  have h4 : a ^ (p - 1) % p = 1 % p := by
    rw[h3]
  have h5 : 1 % p = 1 := by
    have h6 : (p > 1) := by
      apply Nat.Prime.one_lt hp
    apply Nat.mod_eq_of_lt h6 
  rw[h5] at h4  
  assumption

theorem fermat_little_theorem_mod (p : ℕ) (hp : Nat.Prime p) (a : ℕ)(hpneqn : ¬(p ∣ a)) : a ^ (p - 1) ≡ 1 [MOD p] := by
  rw[← Nat.Prime.coprime_iff_not_dvd hp] at hpneqn
  rw[Nat.coprime_iff_gcd_eq_one] at hpneqn
  have h1 : a ^ p ≡ a [MOD p] := fermat_little_theorem' p hp a
  have lem : a * a ^ (p - 1) ≡ a * 1 [MOD p] := by
    have h' : a = a * 1 := by
      simp
    rw[← h']
    have h'' : a ^ p = a * a ^ (p - 1) := by
      have h''' : p - 1 + 1 = p := by
        apply Nat.sub_add_cancel hp.pos
      rw[add_comm] at h'''
      nth_rewrite 1[← h'''] 
      rw[pow_add]
      simp
    rw[← h'']
    assumption 
  apply Nat.ModEq.cancel_left_of_coprime hpneqn lem

theorem RSAMain_mod (p : ℕ) (q : ℕ)(pneqq: p ≠ q)(hp : Nat.Prime p) (hq : Nat.Prime q)(a : ℕ)(hpneqdiva : ¬(p ∣ a))(hqneqdiva : ¬(q ∣ a)) : a ^ (Nat.lcm (p - 1) (q - 1)) ≡ 1 [MOD p * q]:= by
have H1 : ((p - 1) ∣ Nat.lcm (p - 1) (q - 1)) := by
  apply Nat.dvd_lcm_left
have H2 : (q - 1) ∣  Nat.lcm (p - 1) (q - 1) := by
  apply Nat.dvd_lcm_right

have h1 : a ^ (p - 1) ≡ 1 [MOD p] := fermat_little_theorem_mod p hp a hpneqdiva
have h2 : a ^ (q - 1) ≡ 1 [MOD q] := fermat_little_theorem_mod q hq a hqneqdiva

have copq : Nat.coprime p q := by
  rw[← Nat.coprime_primes hp hq] at pneqq
  assumption

have h3 : a ^ Nat.lcm (p - 1) (q - 1) ≡ 1 [MOD p] := by
  have cancel : (p - 1) * (Nat.lcm (p - 1) (q - 1) / (p - 1)) = Nat.lcm (p - 1) (q - 1) := by
    apply Nat.mul_div_cancel' H1
  have cancel' : a ^ ((p - 1) * (Nat.lcm (p - 1) (q - 1) / (p - 1))) ≡ 1 [MOD p] := by
    have pow1 : a ^ ((p - 1) * (Nat.lcm (p - 1) (q - 1) / (p - 1))) ≡ 1 ^ (Nat.lcm (p - 1) (q - 1) / (p - 1)) [MOD p] := by
      have replace : a ^ ((p - 1) * (Nat.lcm (p - 1) (q - 1) / (p - 1))) = (a ^ (p - 1)) ^ (Nat.lcm (p - 1) (q - 1) / (p - 1)) := by
        rw[pow_mul]
      rw[replace]
      apply Nat.ModEq.pow (Nat.lcm (p - 1) (q - 1) / (p - 1)) h1
    have pow1' : 1 ^ ((Nat.lcm (p - 1) (q - 1) / (p - 1))) = 1 := by
      simp
    rw[pow1'] at pow1
    assumption
  rw[cancel] at cancel' 
  assumption

have h3' : a ^ Nat.lcm (p - 1) (q - 1) ≡ 1 [MOD q] := by
  have cancel : (q - 1) * (Nat.lcm (p - 1) (q - 1) / (q - 1)) = Nat.lcm (p - 1) (q - 1) := by
    apply Nat.mul_div_cancel' H2
  have cancel' : a ^ ((q - 1) * (Nat.lcm (p - 1) (q - 1) / (q - 1))) ≡ 1 [MOD q] := by
    have pow1 : a ^ ((q - 1) * (Nat.lcm (p - 1) (q - 1) / (q - 1))) ≡ 1 ^ (Nat.lcm (p - 1) (q - 1) / (q - 1)) [MOD q] := by
      have replace : a ^ ((q - 1) * (Nat.lcm (p - 1) (q - 1) / (q - 1))) = (a ^ (q - 1)) ^ (Nat.lcm (p - 1) (q - 1) / (q - 1)) := by
        rw[pow_mul]
      rw[replace]
      apply Nat.ModEq.pow (Nat.lcm (p - 1) (q - 1) / (q - 1)) h2
    have pow1' : 1 ^ ((Nat.lcm (p - 1) (q - 1) / (q - 1))) = 1 := by
      simp
    rw[pow1'] at pow1
    assumption
  rw[cancel] at cancel' 
  assumption

have h4 : (a ^ Nat.lcm (p - 1) (q - 1) ≡ 1 [MOD p]) ∧ (a ^ Nat.lcm (p - 1) (q - 1) ≡ 1 [MOD q]) := by
  apply And.intro 
  assumption
  assumption

have h5 : a ^ Nat.lcm (p - 1) (q - 1) ≡ 1 [MOD p * q] := by
  rw[Nat.modEq_and_modEq_iff_modEq_mul copq] at h4
  assumption  

assumption

theorem RSAMain (p : ℕ) (q : ℕ)(pneqq: p ≠ q)(hp : Nat.Prime p) (hq : Nat.Prime q)(a : ℕ)(hpneqdiva : ¬(p ∣ a))(hqneqdiva : ¬(q ∣ a)) : a ^ (Nat.lcm (p - 1) (q - 1)) % (p * q) = 1 := by
rw[RSAMain_mod p q pneqq hp hq a hpneqdiva hqneqdiva]
have h1 : (p * q) > 1 := by
  have ppos : 1 < p := by
    apply Nat.Prime.one_lt hp
  have qpos : 1 < q := by
    apply Nat.Prime.one_lt hq
  apply Right.one_lt_mul' ppos qpos
apply Nat.mod_eq_of_lt h1