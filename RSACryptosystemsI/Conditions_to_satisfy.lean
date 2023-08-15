import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Int.GCD
import RSACryptosystemsI.Key_structure
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Dvd


/-- Proof that mod_pow a b n hneq = (a ^ b) % n -/
theorem mod_pow_eq (a : ℕ)(b : ℕ)(n : ℕ)(pos: n ≠ 1)(hneq : n ≠ 0): ModPow a b n hneq = (a ^ b) % n := by
  unfold ModPow
  have h1 : n > 1 := by
    have h1' : (n = 0 ∨ n = 1 ∨ n > 1) := by
      cases n
      · simp only
      · rename_i k
        simp only
        cases k
        · simp only
        · simp only [Nat.succ.injEq, add_eq_zero, and_false, gt_iff_lt, Nat.one_lt_succ_succ, or_true]
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
  · simp only [pow_zero]   
    rw[Nat.mod_eq_of_lt h1]
  · simp only
    rename_i k 
    split
    · rename_i H
      rw[← Nat.add_one k] 
      rw[mod_pow_eq a ((k + 1) / 2) n pos hneq]
      have h : a ^ (k + 1) = a ^ ((k + 1) / 2) * a ^ ((k + 1) / 2) := by
        rw[← pow_add]
        have sum : (k + 1) / 2 + (k + 1) / 2 = k + 1 := by
          have one : 1 % 2 = 1 := by
            simp only
          have odd : (k + 1) % 2 = 0 := by
            rw[← one] at H
            rw[← Nat.ModEq] at H
            have mod : k + 1 ≡ 0 [MOD 2] := by
              apply Nat.ModEq.add_right 1 H
            rw[Nat.ModEq] at mod
            rw[mod]
            simp only
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
        simp only [Nat.mod_mod]
      apply Nat.ModEq.mul H H
    · rw[← Nat.add_one k]
      rw[mod_pow_eq a k n pos hneq]
      have h : a ^ (k + 1) = a ^ k * a := by
        rw[pow_add]
        simp only [pow_one]
      rw[h]
      generalize a ^ k = b
      rw[← Nat.ModEq]
      have comm : a * b = b * a := by
        rw[Nat.mul_comm]
      rw[← comm]
      have H : (b % n) ≡ b [MOD n] := by
        rw[Nat.ModEq]
        simp only [Nat.mod_mod]
      apply Nat.ModEq.mul_left a H
termination_by _ _ => b
decreasing_by
rename_i k h_2 h_1 
rw[← Nat.add_one k] at h_2
have H1 : (k + 1) / 2 < b := by
  simp only [h_2]
  try apply Nat.div_lt_self
  simp only [add_pos_iff, or_true]
  trivial   
have H2 : k < b := by
  simp only [h_2, lt_add_iff_pos_right]
try apply H1
try apply H2

/-- Proof of Freshman's Dream: ((a + b) ^ p) % p = (a ^ p + b ^ p) % p using Binomial Theorem.-/
theorem freshman's_dream (a b : ℕ) (hp : Nat.Prime p) : ((a + b) ^ p) % p = (a ^ p + b ^ p) % p := by
  rw[← Nat.ModEq]
  rw[add_pow]
  rw[Nat.ModEq.comm]
  have h1 : {0, p} ⊆ Finset.range (p + 1) := by 
    rw[Finset.subset_iff]
    simp only [Finset.mem_singleton, Finset.mem_insert, Finset.mem_range, forall_eq_or_imp, add_pos_iff, or_true,forall_eq, lt_add_iff_pos_right, and_self]
  rw[←Finset.sum_sdiff h1]
  have h2 : 0 ≠ p := by 
    intro h3 
    apply Nat.Prime.ne_zero hp
    rw[h3] 
  rw[Finset.sum_pair h2] 
  simp only [Finset.mem_singleton, ge_iff_le, Nat.cast_id, pow_zero, nonpos_iff_eq_zero, tsub_zero, one_mul,
  Nat.choose_zero_right, Nat.cast_one, mul_one, le_refl, tsub_eq_zero_of_le, Nat.choose_self]
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
    simp only [Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_range, add_pos_iff, or_true, Finset.mem_insert, true_or, not_true, and_false] at hi
    simp only [Finset.range, Multiset.range_succ, Finset.mk_cons, Finset.cons_eq_insert, Finset.mem_mk,Multiset.mem_range, lt_self_iff_false, Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_insert] at hi
    cases hi
    rename_i left right 
    cases left 
    · rename_i left'
      rw[left'] at right
      simp only [or_true, not_true] at right
    · rename_i right' 
      assumption
  apply Nat.ModEq.mul_left (a ^ i * b ^ (p - i)) h3

/-- Fermat's Little Theorem: a ^ p ≡ a [MOD p] for prime p.-/
theorem fermat_little_theorem_mod' (p : ℕ) (hp : Nat.Prime p) (a : ℕ) : a ^ p ≡ a [MOD p] := by
  induction a 
  · simp only [Nat.zero_eq, ne_eq]
    have h1 : 0 ^ p = 0 := by
      simp only [ne_eq, zero_pow_eq_zero]
      apply Nat.Prime.pos hp
    simp only [ne_eq, h1]
    trivial 
  · rename_i k base
    rw[← Nat.add_one k]
    have h1 : (k + 1) ^ p ≡ k ^ p + 1 ^ p [MOD p] := by
      apply freshman's_dream
      assumption
    have h2 : k ^ p + 1 ^ p ≡ k ^ p + 1 [MOD p] := by
      simp only [one_pow]
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
      simp only [mul_one]
    rw[← h']
    have h'' : a ^ p = a * a ^ (p - 1) := by
      have h''' : p - 1 + 1 = p := by
        apply Nat.sub_add_cancel hp.pos
      rw[add_comm] at h'''
      nth_rewrite 1[← h'''] 
      rw[pow_add]
      simp only [pow_one, ge_iff_le]
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

/-- RSA Main Theorem: a ^ (lcm (p - 1) (q - 1)) ≡ 1 [MOD p * q] for primes p and q.-/
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
        simp only [ge_iff_le, one_pow]
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
        simp only [ge_iff_le, one_pow]
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
  simp only [ge_iff_le, mul_ite]
  split 
  · rename_i h2
    have neg : Int.natAbs (Nat.xgcd a b).fst = -(Nat.xgcd a b).fst := by
      apply Int.ofNat_natAbs_of_nonpos
      apply Int.le_of_lt h2    
    zify 
    rw[Nat.cast_sub,mul_sub_left_distrib]
    simp only [Int.ofNat_emod, Int.coe_natAbs]
    rw[Int.coe_natAbs] at neg
    rw[neg]
    rw[← Int.ModEq]
    have h3 : a*b ≡ 0 [ZMOD b] := by
      rw[← Int.mul_zero a]
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
    simp only [Nat.cast_one]
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
    simp only [Nat.cast_one] 

/--auxilary lemma to remove the RHS modulo in the above theorem-/
lemma aux_mod (b : ℕ )(hb : b > 1) : 1 % b = 1 := by
  rw[Nat.mod_eq_of_lt hb]


/-- Cyclic nature of powers in mod p i.e If a ^ n = 1, then a ^ b is the same as a ^ c if n∣(c - b) -/
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
        simp only [one_pow]
      rw[obv]
      apply Nat.ModEq.pow (b / n) lem
    have trv : a ^ (b % n) = 1 * a ^ (b % n) := by
      simp only [one_mul]
    nth_rewrite 2[trv]
    apply Nat.ModEq.mul_right (a ^ (b % n)) lem'
  
  have H': a ^ c ≡ a ^ (c % n) [MOD m] := by
    nth_rewrite 1[Euclid]
    rw[pow_add]
    rw[pow_mul]
    have lem' : (a ^ n) ^ (c / n) ≡ 1 [MOD m] := by
      have obv : 1 = 1 ^ (c / n) := by
        simp only [one_pow]
      rw[obv]
      apply Nat.ModEq.pow (c / n) lem
    have trv : a ^ (c % n) = 1 * a ^ (c % n) := by
      simp only [one_mul]
    nth_rewrite 2[trv]
    apply Nat.ModEq.mul_right (a ^ (c % n)) lem'
  rw[h] at H
  have H'' : a ^ (c % n) ≡ a ^ c [MOD m] := by
    apply Nat.ModEq.symm H' 
  apply Nat.ModEq.trans H H''

/-- decryption of an encrypted data -/
def ende (b : Private_key)(m : ℕ) : ℕ := decryption b (encryption b.toPublic_key m) 

/--General fact about how primes not equal to two are greater than or equal to 3-/
theorem prime_three_le_of_ne_two {p : ℕ} (hp : p.Prime) (h_two : 2 ≠ p) : 3 ≤ p := by
  by_contra' h
  revert h_two hp
  match p with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | n + 3 => exact (h.not_le le_add_self).elim

/-- Proof that decryption is correct with some restrictions-/
theorem aux_cipher_correct (b : Private_key)(m : ℕ)(legit : m < b.n)(hpneqdiva : ¬(b.p ∣ m))(hqneqdiva : ¬(b.q ∣ m)) : ende b m = m := by
  have lcm_pos : Nat.lcm (b.p - 1) (b.q - 1) > 1 := by
    have pos : (b.p - 1) > 1 ∨ (b.q - 1) > 1 := by
      by_cases lem : (b.p - 1) > 1
      · exact Or.inl lem
      · have bp2 : b.p = 2 := by
          simp only [ge_iff_le, gt_iff_lt, not_lt, tsub_le_iff_right] at lem
          have : 1 + 1 = 2 := by simp only
          rw[this] at lem
          have : b.p ≥ 2 := by 
            apply Nat.Prime.two_le b.hp
          simp only [ge_iff_le] at this
          have : b.p = 2 := by
            apply Nat.le_antisymm lem this
          assumption
        have bq2 : b.q > 2 := by
          have neq2 : 2 ≠ b.q := by 
            rw[← bp2]
            apply b.ho  
          have : 3 ≤ b.q := by
            apply prime_three_le_of_ne_two b.hq neq2 
          apply LT.lt.gt
          apply this         
        have right : b.q - 1 > 1 := by
          have : 2 = 1 + 1 := by simp only
          rw[this] at bq2
          have : b.q - 1 = Nat.pred b.q := by 
            trivial
          rw[this]
          have : Nat.succ 1 = 1 + 1 := by simp only
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
      simp only [ge_iff_le, ne_eq, tsub_eq_zero_iff_le, not_le, gt_iff_lt]
      apply this
    have qpos : (b.q - 1) ≠ 0 := by
      have : b.q > 1 := by
        apply Nat.Prime.one_lt b.hq
      simp only [ge_iff_le, ne_eq, tsub_eq_zero_iff_le, not_le, gt_iff_lt]
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
  rw[ende]
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
        rw[valueD]
      rw[inv]  
      apply Inverse_mul_one (a.e) (Nat.lcm (b.p - 1) (b.q - 1)) (b.he.right) lcm_pos
    have h2 : m ^ Nat.lcm (b.p - 1) (b.q - 1) ≡ 1 [MOD n] := by
      have : n = b.p * b.q := by
        rw[hn, b.hn]
      rw[this]
      apply RSAMain_mod b.p b.q b.ho b.hp b.hq m hpneqdiva hqneqdiva
    have obv : m ^ 1 = m := by
      simp only [pow_one]
    nth_rewrite 2[← obv]
    apply cyclic m (a.e * b.d) 1 (Nat.lcm (b.p - 1) (b.q - 1)) n h1 h2 lcm_pos 
  rw[Nat.ModEq] at H
  have legit' : m % n = m := by
    apply Nat.mod_eq_of_lt legit
  rw[legit'] at H
  assumption
  exact Nat.ne_of_gt (a.hneq0)
  exact Nat.ne_of_gt (b.toKey_pair.toPublic_key.hneq0)

/--auxilary theorem to show that both p and  q cannot divide the message-/
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
    simp only [h', mul_zero] at hk
    rw[← Nat.le_zero,← not_lt] at hk
    exact hk h0
  exact Nat.not_dvd_of_pos_of_lt kgt0 legit qdvdk

/--auxilary lemma to show that the Modular multiplicative inverse cannot be zero-/
lemma inverse_neq_zero (a : ℕ)(b : ℕ)(hb1 : b ≥  2)(h : Nat.coprime a b) : inverse a b h ≠ 0 := by
  by_contra h'
  rw[inverse] at h'
  simp only [ge_iff_le] at h'
  set x := (Nat.xgcd a b).1 with hx
  have hgcda : x = Nat.gcdA a b := by
    rw[hx, Nat.gcdA]
  have hb : 0 < b := by
    linarith
  have hb2 : b > 1 := by
    linarith
  by_cases h1 : x < 0
  · simp only [h1, ge_iff_le, ite_true, tsub_eq_zero_iff_le] at h'
    rw[← hx] at h' 
    apply Nat.not_lt.mpr h'
    exact Nat.mod_lt (Int.natAbs x) hb
  · simp only [h1, ge_iff_le, ite_false] at h'
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

/-- auxilary lemma which gives a lower bound(2) on φ(n) -/      
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
    have h5 : 2 ∣ (p - 1) := by
      apply Even.two_dvd
      exact Nat.Prime.even_sub_one hp lem
    have h6 : 2 ∣ Nat.lcm (p-1) (q-1) := by
      exact dvd_trans h5 (Nat.dvd_lcm_left (p-1) (q-1))
    have h8 : Nat.lcm (p-1) (q-1) ≠ 0 := by
      apply Nat.lcm_ne_zero
      · by_contra h'
        simp only [ge_iff_le, tsub_eq_zero_iff_le] at h'
        linarith
      · by_contra h'
        simp only [ge_iff_le, tsub_eq_zero_iff_le] at h'
        linarith
    exact Nat.le_of_dvd (Nat.zero_lt_of_ne_zero h8) h6
  · push_neg at lem
    rw[lem]
    simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub, tsub_zero, Nat.lcm_one_left]
    have h3 : q > 2 := by
      linarith
    have h4 : 3 -1 = 2 := by
      simp only
    rw[← h4]
    apply Nat.sub_le_sub_right
    exact h3

/--second auxilary lemma to show the decryption is correct -/
theorem aux_cipher_correct_2 (b : Private_key)(m : ℕ)(legit : m < b.n)(hpneqdiva : b.p ∣ m)(h0 : m > 0) : ende b m = m := by
  rw[ende]
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
      simp only at he 
      rw[b.hd,valueD]
      simp only [ge_iff_le, ne_eq]
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
        simp only at he 
        rw[b.hd,valueD]
        simp only [ge_iff_le, ne_eq]
        apply inverse_neq_zero
        apply phi_inequality b.p b.q b.hp b.hq b.ho
      have tri : 1 = Nat.succ 0 := by simp only
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
          rw[b.hd,valueD]
          simp only [ge_iff_le]
          apply Nat.ModEq.of_dvd (Nat.dvd_lcm_right (b.p-1) (b.q-1)) 
          rw[Nat.ModEq,Inverse_mul_one]
          have bro : Nat.lcm (b.p-1) (b.q-1) ≥ 2 := phi_inequality b.p b.q b.hp b.hq b.ho
          have bro1 : 2 = Nat.succ 1 := by simp only
          rw[bro1] at bro
          simp only [ge_iff_le] at bro
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
              simp only at he 
              rw[b.hd,valueD]
              simp only [ge_iff_le, ne_eq]
              apply inverse_neq_zero
              apply phi_inequality b.p b.q b.hp b.hq b.ho
            have tri : 1 = Nat.succ 0 := by simp only
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
        simp only [ge_iff_le, one_pow]
      nth_rewrite 4[this]
      apply Nat.ModEq.pow 
      apply fermat
    have mod_1' : m ^ (a.e * b.d - 1) * m ≡ 1 * m [MOD b.q] := by
      apply Nat.ModEq.mul_right m mod_1
    have : 1 * m = m := by simp only [one_mul]
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

/--auxilary lemma to prove trivial properties of the new-formed Private_key -/
lemma Private_key_gen_aux(b : Private_key)(p : ℕ)(q : ℕ)(hp : Nat.Prime p)(hq : Nat.Prime q)(ho : p ≠ q)(e : ℕ )(he1 : Nat.coprime e (Nat.lcm (p - 1) (q - 1)))(he2 : 2 < e)(hmain : b = PrivateKeyGen p q hp hq ho e he1 he2) : b.p = p ∧ b.q = q:= by 
  apply And.intro
  · rw[hmain]
    unfold PrivateKeyGen
    simp only
    unfold KeyGeneration
    simp only
  · rw[hmain]
    unfold PrivateKeyGen
    simp only
    unfold KeyGeneration
    simp only

/--auxilary lemma to show that the newly formed Private_key share the same natural number-/
lemma Private_key_gen_aux_n(b : Private_key)(b1 : Private_key)(he1 : Nat.coprime b.e (Nat.lcm (b.q - 1) (b.p - 1)))(ho : b.q ≠ b.p)(hmain : b1 = PrivateKeyGen b.q b.p b.hq b.hp ho b.e he1 b.he.1) : b.n = b1.n := by 
  rw[hmain]
  unfold PrivateKeyGen
  simp only
  unfold KeyGeneration
  simp only
  rw[b.hn,mul_comm]

/-- auxilary lemma to show that the newly formed Private_key shares the same encryption moduli(e)-/
lemma Private_key_gen_aux_e (b : Private_key)(b1 : Private_key)(he1 : Nat.coprime b.e (Nat.lcm (b.q - 1) (b.p - 1)))(ho : b.q ≠ b.p)(hmain : b1 = PrivateKeyGen b.q b.p b.hq b.hp ho b.e he1 b.he.1) : b1.e = b.e := by
  rw[hmain]
  unfold PrivateKeyGen
  simp only
  unfold KeyGeneration
  simp only


/-- auxilary lemma to show that the newly formed Private_key shares the same decryption moduli(d) -/
lemma Private_key_gen_aux_d (b : Private_key)(b1 : Private_key)(he1 : Nat.coprime b.e (Nat.lcm (b.q - 1) (b.p - 1)))(ho : b.q ≠ b.p)(hmain : b1 = PrivateKeyGen b.q b.p b.hq b.hp ho b.e he1 b.he.1) : b1.d = b.d := by
  rw[b1.hd,b.hd,valueD, valueD]
  simp only [ge_iff_le]
  have helemma : b1.e = b.e := by 
    apply Private_key_gen_aux_e b b1 he1 ho hmain
  have hplemma : b.p = b1.q := ((Private_key_gen_aux b1 b.q b.p b.hq b.hp (Ne.symm b.ho) b.e he1 b.he.1 hmain).2).symm
  have hqlemma : b.q = b1.p := ((Private_key_gen_aux b1 b.q b.p b.hq b.hp (Ne.symm b.ho) b.e he1 b.he.1 hmain).1).symm
  conv in b1.toKey_pair.toPublic_key.e => rw[helemma]
  have hlcm : Nat.lcm (b1.p - 1) (b1.q - 1) = Nat.lcm (b.p - 1) (b.q - 1) := by
    rw[hplemma,hqlemma,Nat.lcm_comm]
  conv in Nat.lcm (b1.toKey_pair.p - 1) (b1.toKey_pair.q - 1) => rw[hlcm]


/-- auxilary lemma to show that the newly formed Private_key has the same Public_key structure as the original Key-/
lemma Private_key_gen_aux_Public_key(b : Private_key)(b1 : Private_key)(he1 : Nat.coprime b.e (Nat.lcm (b.q - 1) (b.p - 1)))(ho : b.q ≠ b.p)(hmain : b1 = PrivateKeyGen b.q b.p b.hq b.hp ho b.e he1 b.he.1) : b.toKey_pair.toPublic_key = b1.toKey_pair.toPublic_key:= by 
  rw[hmain]
  unfold PrivateKeyGen
  simp only
  unfold KeyGeneration
  simp only
  apply Public_key.ext
  simp only
  rw[b.hn,mul_comm]
  simp only

/--auxilary lemma to show that the newly formed Private_key gives the same value when going through encryption and then decryption-/
lemma Private_key_gen_aux_ende_eq (b : Private_key)(b1 : Private_key)(he1 : Nat.coprime b.e (Nat.lcm (b.q - 1) (b.p - 1)))(ho : b.q ≠ b.p)(hmain : b1 = PrivateKeyGen b.q b.p b.hq b.hp ho b.e he1 b.he.1)(m : ℕ) : ende b m = ende b1 m := by 
  rw[ende,ende,decryption,decryption]
  have hdmain : b1.d = b.d := by
    apply Private_key_gen_aux_d b b1 he1 ho hmain
  rw[hdmain]
  have hPublic_key : b.toKey_pair.toPublic_key = b1.toKey_pair.toPublic_key := by
    apply Private_key_gen_aux_Public_key b b1 he1 ho hmain
  conv in b.toKey_pair.toPublic_key => rw[hPublic_key]
  have hn : b.n = b1.n := by
    apply Private_key_gen_aux_n b b1 he1 ho hmain
  conv in b.n => rw[hn]

/--Proof of correctness of the encryption for a message not equal to 0-/
theorem cipher_correct_m_gt_0 (b : Private_key)(m : ℕ)(legit : m < b.n)(h0 : m > 0) : ende b m = m := by 
  by_cases h : ¬(b.p ∣ m) ∧ ¬(b.q ∣ m) 
  · apply aux_cipher_correct b m legit h.1 h.2
  · rw[not_and_or,not_not,not_not] at h
    wlog h' : b.p ∣ m 
    · 
      have he1 : Nat.coprime b.e (Nat.lcm (b.q - 1) (b.p - 1)) := by 
        have triv : Nat.lcm (b.q - 1) (b.p - 1) = Nat.lcm (b.p - 1) (b.q - 1) := by
          rw[Nat.lcm_comm]
        rw[triv]
        apply b.he.2
      set b1 := PrivateKeyGen b.q b.p b.hq b.hp (Ne.symm b.ho) b.e he1 b.he.1 with hb1
      have hplemma : b.p = b1.q := ((Private_key_gen_aux b1 b.q b.p b.hq b.hp (Ne.symm b.ho) b.e he1 b.he.1 hb1).2).symm
      have hqlemma : b.q = b1.p := ((Private_key_gen_aux b1 b.q b.p b.hq b.hp (Ne.symm b.ho) b.e he1 b.he.1 hb1).1).symm
      have hnlemma : b1.n = b.n := by 
        rw[b1.hn,b.hn]
        rw[hplemma,hqlemma,mul_comm]
      rw[hnlemma.symm] at legit
      rw[hplemma,hqlemma] at h
      rw[hplemma] at h'
      have hpmain : b1.p ∣ m := (or_iff_right h').mp h
      rw[or_comm] at h
      have finalmain : ende b m = ende b1 m := by
        apply Private_key_gen_aux_ende_eq b b1 he1 (Ne.symm b.ho) hb1 m
      rw[finalmain]
      apply this b1 m legit h0 h hpmain     
    · apply aux_cipher_correct_2 b m legit h' h0

/--Proof of correctness of the encryption-/
theorem cipher_correct(b : Private_key)(m : ℕ)(legit : m < b.n) : ende b m = m := by
  by_cases h0 : m = 0
  · rw[h0]
    have hn : b.n > 1 := by 
      rw[b.hn]
      apply Right.one_lt_mul' (Nat.Prime.one_lt b.hp) (Nat.Prime.one_lt b.hq)
    simp only [ende, decryption,encryption]
    rw[mod_pow_eq,mod_pow_eq]
    have he : b.e > 0 := by
      have he1 : b.e > 2 := (b.he).1
      linarith
    rw[zero_pow he,Nat.zero_mod]
    have hd : b.d > 0 := by 
      apply Nat.zero_lt_of_ne_zero
      rw[b.hd,valueD]
      simp only [ge_iff_le, ne_eq]
      apply inverse_neq_zero
      apply phi_inequality b.p b.q b.hp b.hq b.ho
    rw[zero_pow hd,Nat.zero_mod]
    all_goals apply ne_of_gt hn
  · push_neg at h0
    rw[← Nat.pos_iff_ne_zero] at h0 
    apply cipher_correct_m_gt_0 b m legit h0



