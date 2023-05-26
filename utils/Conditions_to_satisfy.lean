import Mathlib
import RSACryptosystemsI

/-- Proof that mod_pow a b n hneq = (a ^ b) % n -/
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
    rename_i k 
    split
    · rename_i H
      rw[← Nat.add_one k] 
      rw[mod_pow_eq a ((k + 1) / 2) n pos hneq]
      have h : a ^ (k + 1) = a ^ ((k + 1) / 2) * a ^ ((k + 1) / 2) := by
        rw[← pow_add]
        have sum : (k + 1) / 2 + (k + 1) / 2 = k + 1 := by
          have one : 1 % 2 = 1 := by
            simp
          have odd : (k + 1) % 2 = 0 := by
            rw[← one] at H
            rw[← Nat.ModEq] at H
            have mod : k + 1 ≡ 0 [MOD 2] := by
              apply Nat.ModEq.add_right 1 H
            rw[Nat.ModEq] at mod
            rw[mod]
            simp
          have dvd : 2 ∣ (k + 1) := by
            apply Nat.dvd_of_mod_eq_zero
            assumption
          have eq : 2 * ((k + 1)/ 2) = k + 1 := by
             rw[Nat.mul_div_cancel_left' dvd]
          have twice : (k + 1) / 2 + (k + 1) / 2 = 2 * ((k + 1) / 2) := by
             rw[← Nat.mul_two, Nat.mul_comm]
          rw[eq] at twice
          assumption
        rw[sum]
      rw[h]
      generalize a ^ ((k + 1) / 2) = b
      rw[← Nat.ModEq]
      have H : (b % n) ≡ b [MOD n] := by
        rw[Nat.ModEq]
        simp
      apply Nat.ModEq.mul H H
    · rw[← Nat.add_one k]
      rw[mod_pow_eq a k n pos hneq]
      have h : a ^ (k + 1) = a ^ k * a := by
        rw[pow_add]
        simp
      rw[h]
      generalize a ^ k = b
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
rename_i k h_2 h_1 
rw[← Nat.add_one k] at h_2
have H1 : (k + 1) / 2 < b := by
  simp[h_2]
  try apply Nat.div_lt_self
  simp
  trivial   
have H2 : k < b := by
  simp[h_2]
try apply H1
try apply H2

/-- Proof of Freshman's Dream: ((a + b) ^ p) % p = (a ^ p + b ^ p) % p using Binomial Theorem.-/
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

/-- Fermat's Little Theorem: a ^ p ≡ a [MOD p] for prime p.-/
theorem fermat_little_theorem_mod' (p : ℕ) (hp : Nat.Prime p) (a : ℕ) : a ^ p ≡ a [MOD p] := by
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

/-- Fermat's Little Theorem: a ^ (p - 1) ≡ 1 [MOD p] for prime p.-/
theorem fermat_little_theorem_mod (p : ℕ) (hp : Nat.Prime p) (a : ℕ)(hpneqn : ¬(p ∣ a)) : a ^ (p - 1) ≡ 1 [MOD p] := by
  rw[← Nat.Prime.coprime_iff_not_dvd hp] at hpneqn
  rw[Nat.coprime_iff_gcd_eq_one] at hpneqn
  have h1 : a ^ p ≡ a [MOD p] := fermat_little_theorem_mod' p hp a
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

/-- Fermat's Little Theorem: a ^ (p - 1) % p = 1 for prime p.-/
theorem fermat_little_theorem (p : ℕ) (hp : Nat.Prime p) (a : ℕ)(hpneqn : ¬(p ∣ a)) : a ^ (p - 1) % p = 1 := by 
  have h3 : a ^ (p - 1) ≡ 1 [MOD p] := by 
    apply fermat_little_theorem_mod p hp a hpneqn
  have h4 : a ^ (p - 1) % p = 1 % p := by
    rw[h3]
  have h5 : 1 % p = 1 := by
    have h6 : (p > 1) := by
      apply Nat.Prime.one_lt hp
    apply Nat.mod_eq_of_lt h6 
  rw[h5] at h4  
  assumption

/-- RSA Main Theorem: a ^ (lcm (p - 1) (q - 1)) ≡ 1 [MOD p * q] for prime p and q.-/
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

/-- RSA Main Theorem: a ^ (lcm (p - 1) (q - 1)) % (p * q) = 1 for primes p and q.-/
theorem RSAMain (p : ℕ) (q : ℕ)(pneqq: p ≠ q)(hp : Nat.Prime p) (hq : Nat.Prime q)(a : ℕ)(hpneqdiva : ¬(p ∣ a))(hqneqdiva : ¬(q ∣ a)) : a ^ (Nat.lcm (p - 1) (q - 1)) % (p * q) = 1 := by
  rw[RSAMain_mod p q pneqq hp hq a hpneqdiva hqneqdiva]
  have h1 : (p * q) > 1 := by
    have ppos : 1 < p := by
      apply Nat.Prime.one_lt hp
    have qpos : 1 < q := by
      apply Nat.Prime.one_lt hq
    apply Right.one_lt_mul' ppos qpos
  apply Nat.mod_eq_of_lt h1

/-- Proof of correctness of inverse function.-/
theorem Inverse_mul_one (a : ℕ)(b : ℕ)(h : Nat.coprime a b)(h1 : b > 1) : (a * (inverse a b h) ) % b = 1 % b := by
  rw[inverse]
  simp
  split 
  · rename_i h2
    have neg : Int.natAbs (Nat.xgcd a b).fst = -(Nat.xgcd a b).fst := by
      apply Int.ofNat_natAbs_of_nonpos
      apply Int.le_of_lt h2    
    zify 
    rw[Nat.cast_sub,mul_sub_left_distrib]
    simp 
    rw[Int.coe_natAbs] at neg
    rw[neg]
    rw[← Int.ModEq]
    have h3 : a*b ≡ 0 [ZMOD b] := by
      rw[← Int.mul_zero a]
      have h4 : a ≡ a [ZMOD b] := by
        exact Int.ModEq.rfl
      apply Int.ModEq.mul_left
      rw[Int.modEq_zero_iff_dvd]
    rw[Int.sub_eq_add_neg]
    rw[← zero_add 1] 
    apply Int.ModEq.add h3 
    rw[Int.ModEq]
    rw[← neg_mul]
    rw[Int.mul_emod,Int.emod_emod, ←Int.mul_emod,mul_neg,neg_mul,neg_neg]
    rw[← Nat.gcdA]
    have h4 : (Nat.gcd a b) = a * Nat.gcdA a b + b * Nat.gcdB a b := by 
      apply Nat.gcd_eq_gcd_ab a b
    rw[Nat.coprime] at h
    rw[h] at h4 
    have lem : a * Nat.gcdA a b % b = (a * Nat.gcdA a b + b * Nat.gcdB a b) % b := by 
      exact (Int.add_mul_emod_self_left (a * Nat.gcdA a b) b (Nat.gcdB a b)).symm
    rw[lem]
    rw[← h4]
    simp
    have lem : b > 0 := by linarith
    set r := Int.natAbs (Nat.xgcd a b).fst with ha
    apply le_of_lt
    exact Nat.mod_lt r lem
  · rename_i h2 
    have pos : Int.natAbs (Nat.xgcd a b).fst = (Nat.xgcd a b).fst := by
      apply Int.natAbs_of_nonneg
      linarith
    zify
    zify at pos
    rw[pos]
    rw[Int.mul_emod,Int.emod_emod, ←Int.mul_emod]
    rw[← Nat.gcdA]
    have h4 : (Nat.gcd a b) = a * Nat.gcdA a b + b * Nat.gcdB a b := by 
      apply Nat.gcd_eq_gcd_ab a b
    rw[Nat.coprime] at h
    rw[h] at h4 
    have lem : a * Nat.gcdA a b % b = (a * Nat.gcdA a b + b * Nat.gcdB a b) % b := by 
      exact (Int.add_mul_emod_self_left (a * Nat.gcdA a b) b (Nat.gcdB a b)).symm
    rw[lem]
    rw[← h4]
    simp 

lemma aux_mod (b : ℕ )(hb : b > 1) : 1 % b = 1 := by
  rw[Nat.mod_eq_of_lt hb]
/-- If a ^ n = 1, then a ^ b is the same as a ^ c if n∣(c - b) -/
theorem cyclic (a : ℕ)(b : ℕ)(c : ℕ)(n : ℕ)(m : ℕ)(h : b % n = c % n)(lem : a ^ n ≡ 1 [MOD m])(hneq : n > 1) : a ^ b ≡ a ^ c [MOD m]:= by
  have euclid' : n * (b / n) + (b % n) = b := by
    apply Nat.div_add_mod b n
  have euclid : b = n * (b / n) + (b % n) := by
    rw[euclid']

  have Euclid' : n * (c / n) + (c % n) = c := by
    apply Nat.div_add_mod c n
  have Euclid : c = n * (c / n) + (c % n) := by
    rw[Euclid']
  
  have H: a ^ b ≡ a ^ (b % n) [MOD m] := by
    nth_rewrite 1[euclid]
    rw[pow_add]
    rw[pow_mul]
    have lem' : (a ^ n) ^ (b / n) ≡ 1 [MOD m] := by
      have obv : 1 = 1 ^ (b / n) := by
        simp
      rw[obv]
      apply Nat.ModEq.pow (b / n) lem
    have trv : a ^ (b % n) = 1 * a ^ (b % n) := by
      simp
    nth_rewrite 2[trv]
    apply Nat.ModEq.mul_right (a ^ (b % n)) lem'
  
  have H': a ^ c ≡ a ^ (c % n) [MOD m] := by
    nth_rewrite 1[Euclid]
    rw[pow_add]
    rw[pow_mul]
    have lem' : (a ^ n) ^ (c / n) ≡ 1 [MOD m] := by
      have obv : 1 = 1 ^ (c / n) := by
        simp
      rw[obv]
      apply Nat.ModEq.pow (c / n) lem
    have trv : a ^ (c % n) = 1 * a ^ (c % n) := by
      simp
    nth_rewrite 2[trv]
    apply Nat.ModEq.mul_right (a ^ (c % n)) lem'
  rw[h] at H
  have H'' : a ^ (c % n) ≡ a ^ c [MOD m] := by
    apply Nat.ModEq.symm H' 
  apply Nat.ModEq.trans H H''

/-- decryption of an encrypted data -/
def message' (b : Private_key)(m : ℕ) : ℕ := decryption b (encryption b.toPublic_key m) 

theorem Prime.three_le_of_ne_two {p : ℕ} (hp : p.Prime) (h_two : 2 ≠ p) : 3 ≤ p := by
  by_contra' h
  revert h_two hp
  match p with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | n + 3 => exact (h.not_le le_add_self).elim

/-- Proof that decryption is correct-/
theorem cipher_correct (b : Private_key)(m : ℕ)(legit : m < b.n)(hpneqdiva : ¬(b.p ∣ m))(hqneqdiva : ¬(b.q ∣ m)) : message' b m = m := by
  have lcm_pos : Nat.lcm (b.p - 1) (b.q - 1) > 1 := by
    have pos : (b.p - 1) > 1 ∨ (b.q - 1) > 1 := by
      by_cases lem : (b.p - 1) > 1
      · exact Or.inl lem
      · have bp2 : b.p = 2 := by
          simp at lem
          have : 1 + 1 = 2 := by simp
          rw[this] at lem
          have : b.p ≥ 2 := by 
            apply Nat.Prime.two_le b.hp
          simp at this
          have : b.p = 2 := by
            apply Nat.le_antisymm lem this
          assumption
        have bq2 : b.q > 2 := by
          have neq2 : 2 ≠ b.q := by 
            rw[← bp2]
            apply b.ho  
          have : 3 ≤ b.q := by
            apply Prime.three_le_of_ne_two b.hq neq2 
          apply LT.lt.gt
          apply this         
        have right : b.q - 1 > 1 := by
          have : 2 = 1 + 1 := by simp
          rw[this] at bq2
          have : b.q - 1 = Nat.pred b.q := by 
            trivial
          rw[this]
          have : Nat.succ 1 = 1 + 1 := by simp
          rw[← this] at bq2
          apply LT.lt.gt
          have :  Nat.succ 1 < b.q := by
            apply LT.lt.gt bq2
          rw[Nat.lt_pred_iff]
          apply this
        exact Or.inr right
    have ppos : (b.p - 1) ≠ 0 := by
      have : b.p > 1 := by
        apply Nat.Prime.one_lt b.hp
      simp
      apply this
    have qpos : (b.q - 1) ≠ 0 := by
      have : b.q > 1 := by
        apply Nat.Prime.one_lt b.hq
      simp
      apply this    
    cases pos
    · rename_i h
      have : Nat.lcm (b.p - 1) (b.q - 1) ≥ (b.p - 1) := by
        apply Nat.le_of_dvd 
        have : Nat.lcm (b.p - 1) (b.q - 1) ≠ 0 := by
          apply Nat.lcm_ne_zero ppos qpos
        apply Nat.pos_of_ne_zero this
        apply Nat.dvd_lcm_left
      linarith 
    · rename_i h
      have : Nat.lcm (b.p - 1) (b.q - 1) ≥ (b.q - 1) := by
        apply Nat.le_of_dvd 
        have : Nat.lcm (b.p - 1) (b.q - 1) ≠ 0 := by
          apply Nat.lcm_ne_zero ppos qpos
        apply Nat.pos_of_ne_zero this
        apply Nat.dvd_lcm_right
      linarith
  rw[message']
  rw[decryption]
  rw[mod_pow_eq]
  set n := b.toKey_pair.toPublic_key.n with hn
  set a := b.toKey_pair.toPublic_key
  rw[encryption]
  rw[mod_pow_eq]
  rw[← hn, ←Nat.pow_mod, ←pow_mul]
  have H : m ^ (a.e * b.d) ≡ m [MOD n] := by
    have h1 : a.e * b.d % Nat.lcm (b.p - 1) (b.q - 1) = 1 % Nat.lcm (b.p - 1) (b.q - 1):= by
      have inv : b.d = inverse a.e (Nat.lcm (b.p - 1) (b.q - 1)) (b.he.right) := by
        rw[b.hd] 
        rw[value_d]
      rw[inv]  
      apply Inverse_mul_one (a.e) (Nat.lcm (b.p - 1) (b.q - 1)) (b.he.right) lcm_pos
    have h2 : m ^ Nat.lcm (b.p - 1) (b.q - 1) ≡ 1 [MOD n] := by
      have : n = b.p * b.q := by
        rw[hn, b.hn]
      rw[this]
      apply RSAMain_mod b.p b.q b.ho b.hp b.hq m hpneqdiva hqneqdiva
    have obv : m ^ 1 = m := by
      simp
    nth_rewrite 2[← obv]
    apply cyclic m (a.e * b.d) 1 (Nat.lcm (b.p - 1) (b.q - 1)) n h1 h2 lcm_pos 
  rw[Nat.ModEq] at H
  have legit' : m % n = m := by
    apply Nat.mod_eq_of_lt legit
  rw[legit'] at H
  assumption
  exact Nat.ne_of_gt (a.hneq0)
  exact Nat.ne_of_gt (b.toKey_pair.toPublic_key.hneq0)

theorem pq_both_not_dvd (b : Private_key)(m : ℕ)(legit : m < b.n)(hpneqdiva : b.p ∣ m)(h0 : m > 0) : ¬ (b.q ∣ m) := by
  by_contra h
  have hpqcoprime : Nat.coprime b.q b.p := by
    rw[Nat.coprime_primes b.hq b.hp]
    by_contra h'
    exact b.ho h'.symm
  rw[dvd_iff_exists_eq_mul_left] at hpneqdiva
  have hn : b.n = b.p * b.q := by
    rw[b.hn]
  rw[hn] at legit
  cases hpneqdiva
  rename_i hk
  rename_i k
  rw[mul_comm] at hk
  rw[hk] at legit
  have pgt0 : b.p > 0 := by
    apply Nat.Prime.pos b.hp
  rw[mul_lt_mul_left pgt0] at legit
  have qdvdk : b.q ∣ k := by
    rw[hk] at h
    exact Nat.coprime.dvd_of_dvd_mul_left hpqcoprime h
  have kgt0 : k > 0 := by
    by_contra h'
    rw[not_lt,Nat.le_zero] at h'
    simp[h'] at hk
    rw[← Nat.le_zero,← not_lt] at hk
    exact hk h0
  exact Nat.not_dvd_of_pos_of_lt kgt0 legit qdvdk


lemma inverse_neq_zero (a : ℕ)(b : ℕ)(hb1 : b ≥  2)(h : Nat.coprime a b) : inverse a b h ≠ 0 := by
  by_contra h'
  rw[inverse] at h'
  simp at h'
  set x := (Nat.xgcd a b).1 with hx
  have hgcda : x = Nat.gcdA a b := by
    rw[hx, Nat.gcdA]
  have hb : 0 < b := by
    linarith
  have hb2 : b > 1 := by
    linarith
  by_cases h1 : x < 0
  · simp[h1] at h'
    rw[← hx] at h' 
    apply Nat.not_lt.mpr h'
    exact Nat.mod_lt (Int.natAbs x) hb
  · simp[h1] at h'
    rw[← hx] at h'
    rw[not_lt] at h1
    rw[← Nat.dvd_iff_mod_eq_zero, ← Int.ofNat_dvd_left] at h'
    have bezout : a * x + b * (Nat.gcdB a b) = Nat.gcd a b := by
      rw[hgcda,Nat.gcd_eq_gcd_ab]
    rw[h] at bezout
    have ha : (b : ℤ)  ∣ (a:ℤ) * x := by
      apply dvd_mul_of_dvd_right h'
    have hrefl : (b : ℤ) ∣  b * (Nat.gcdB a b) := by
      apply dvd_mul_of_dvd_left
      exact dvd_rfl
    have hdiv : (b : ℤ) ∣ (a : ℤ) * x + b * (Nat.gcdB a b) := by
      apply dvd_add ha hrefl
    rw[bezout] at hdiv
    zify at hb
    have hcontra : (b : ℤ)  = 1 := by
      apply Int.eq_one_of_dvd_one (le_of_lt hb) hdiv
    linarith
      
lemma phi_inequality(p : ℕ )(q : ℕ)(hp : Nat.Prime p)(hq : Nat.Prime q )(ho : p ≠ q) : Nat.lcm (p - 1) (q - 1) ≥ 2 := by 
  wlog h : p < q 
  push_neg at h
  have hh : q < p := by
    rw[Nat.lt_iff_le_and_ne]
    constructor
    ·exact h
    ·exact ho.symm 
  rw[Nat.lcm_comm]
  exact this q p hq hp ho.symm hh 
  have h1 : q ≥ 2 := by
    apply Nat.Prime.two_le hq
  have h2 : p ≥ 2 := by
    apply Nat.Prime.two_le hp 
  by_cases lem : p ≠ 2
  · 
    have h3 : 2 < p := by
      rw[Nat.lt_iff_le_and_ne]
      constructor
      ·exact h2
      ·exact lem.symm
    have h4 : q > 2 := by
      linarith
    have h7 : q ≠ 2 := by
      intro h'
      rw[h'] at h4
      linarith
    have h5 : 2 ∣ (p - 1) := by
      apply Even.two_dvd
      exact Nat.Prime.even_sub_one hp lem
    have h6 : 2 ∣ Nat.lcm (p-1) (q-1) := by
      exact dvd_trans h5 (Nat.dvd_lcm_left (p-1) (q-1))
    have h8 : Nat.lcm (p-1) (q-1) ≠ 0 := by
      apply Nat.lcm_ne_zero
      · by_contra h'
        simp at h'
        linarith
      · by_contra h'
        simp at h'
        linarith
    exact Nat.le_of_dvd (Nat.zero_lt_of_ne_zero h8) h6
  · push_neg at lem
    rw[lem]
    simp
    have h3 : q > 2 := by
      linarith
    have h4 : 3 -1 = 2 := by
      simp
    rw[← h4]
    apply Nat.sub_le_sub_right
    exact h3
    
theorem cipher_correct' (b : Private_key)(m : ℕ)(legit : m < b.n)(hpneqdiva : b.p ∣ m)(h0 : m > 0) : message' b m = m := by
  rw[message']
  rw[decryption]
  rw[mod_pow_eq]
  set n := b.toKey_pair.toPublic_key.n with hn
  set a := b.toKey_pair.toPublic_key
  rw[encryption]
  rw[mod_pow_eq]
  rw[← hn, ←Nat.pow_mod, ←pow_mul]
  have Hp : m ^ (a.e * b.d) ≡ m [MOD b.p] := by
    have dvd : b.p ∣ m ^ (a.e * b.d) := by
      apply dvd_pow
      apply hpneqdiva
      apply mul_ne_zero
      by_contra h'
      have he : a.e > 2 := b.he.1
      rw[h'] at he
      simp at he 
      rw[b.hd,value_d]
      simp
      apply inverse_neq_zero
      apply phi_inequality b.p b.q b.hp b.hq b.ho
    have h1 : m ^ (a.e * b.d) ≡ 0 [MOD b.p] := by
      apply Nat.mod_eq_zero_of_dvd dvd
    have h2 : m ≡ 0 [MOD b.p] := by
      apply Nat.mod_eq_zero_of_dvd hpneqdiva
    rw[Nat.ModEq.comm] at h2
    apply Nat.ModEq.trans h1 h2 
  have Hq : m ^ (a.e * b.d) ≡ m [MOD b.q] := by
    have trv : a.e * b.d = a.e * b.d - 1 + 1 := by
      rw[Nat.sub_add_cancel]
      have lemm :0 < a.e * b.d  := by
        rw[Nat.pos_iff_ne_zero]
        apply mul_ne_zero
        by_contra h'
        have he : a.e > 2 := b.he.1
        rw[h'] at he
        simp at he 
        rw[b.hd,value_d]
        simp
        apply inverse_neq_zero
        apply phi_inequality b.p b.q b.hp b.hq b.ho
      have tri : 1 = Nat.succ 0 := by simp
      rw[tri]
      rw[Nat.succ_le]
      assumption
    rw[trv]
    rw[pow_add]
    rw[pow_one]
    have mod_1 : m ^ (a.e * b.d - 1) ≡ 1 [MOD b.q] := by
      have fermat : m ^ (b.q - 1) ≡ 1 [MOD b.q] := by
        apply fermat_little_theorem_mod
        apply b.hq
        apply pq_both_not_dvd b m legit hpneqdiva
        exact h0
      have : (b.q - 1) ∣ (a.e * b.d - 1) := by
        have : a.e * b.d ≡ 1 [MOD (b.q - 1)] := by
          rw[b.hd,value_d]
          simp
          apply Nat.ModEq.of_dvd (Nat.dvd_lcm_right (b.p-1) (b.q-1)) 
          rw[Nat.ModEq,Inverse_mul_one]
          have bro : Nat.lcm (b.p-1) (b.q-1) ≥ 2 := phi_inequality b.p b.q b.hp b.hq b.ho
          have bro1 : 2 = Nat.succ 1 := by simp
          rw[bro1] at bro
          simp at bro
          rw[Nat.succ_le] at bro
          exact bro
        have : a.e * b.d - 1 ≡ 0 [MOD (b.q - 1)] := by
          have lemmar : 1 ≤ a.e *b.d := by 
            have lemm : 0 < a.e * b.d  := by
              rw[Nat.pos_iff_ne_zero]
              apply mul_ne_zero
              by_contra h'
              have he : a.e > 2 := b.he.1
              rw[h'] at he
              simp at he 
              rw[b.hd,value_d]
              simp
              apply inverse_neq_zero
              apply phi_inequality b.p b.q b.hp b.hq b.ho
            have tri : 1 = Nat.succ 0 := by simp
            rw[tri]
            rw[Nat.succ_le]
            assumption
          rw[Nat.ModEq.comm,Nat.modEq_iff_dvd' lemmar] at this     
          rw[Nat.modEq_zero_iff_dvd]
          assumption
        rw[Nat.modEq_zero_iff_dvd] at this
        assumption
      have : (a.e * b.d - 1) = (b.q - 1) * ((a.e * b.d - 1) / (b.q - 1)) := by
        rw[Nat.mul_div_cancel' this]
      rw[this]
      rw[pow_mul]
      have : 1 = 1 ^ ((a.e * b.d - 1) / (b.q - 1)) := by
        simp
      nth_rewrite 4[this]
      apply Nat.ModEq.pow 
      apply fermat
    have mod_1' : m ^ (a.e * b.d - 1) * m ≡ 1 * m [MOD b.q] := by
      apply Nat.ModEq.mul_right m mod_1
    have : 1 * m = m := by simp
    rw[this] at mod_1'
    apply mod_1'
  have H : m ^ (a.e * b.d) ≡ m [MOD n] := by
    have : n = b.p * b.q := by
      rw[hn, b.hn]
    rw[this]
    have hpq : Nat.coprime b.p b.q := by
      rw[Nat.coprime_primes]
      apply b.ho 
      apply b.hp
      apply b.hq
    have Hpq : m ^ (a.e * b.d) ≡ m [MOD b.p] ∧ m ^ (a.e * b.d) ≡ m [MOD b.q] := by
      apply And.intro 
      assumption
      assumption
    rw[Nat.modEq_and_modEq_iff_modEq_mul hpq] at Hpq
    assumption
  rw[Nat.ModEq] at H
  have legit' : m % n = m := by
    apply Nat.mod_eq_of_lt legit
  rw[legit'] at H
  assumption
  exact Nat.ne_of_gt (a.hneq0)
  exact Nat.ne_of_gt (b.toKey_pair.toPublic_key.hneq0)
