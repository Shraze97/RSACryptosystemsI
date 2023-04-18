import Mathlib
import Init 


   
def mod_pow (a : ℕ)(b : ℕ)(n : ℕ) : ℕ :=
  match b with 
  | 0 => 1
  | Nat.succ k=> 
    if k % 2 = 0 then 
    let c := mod_pow a ((k + 1)/2) n 
    (c * c) % n
  else 
    (a * (mod_pow a k n )) % n
termination_by _ _ => b
decreasing_by      
simp 
have h3 : (k + 1)/2  < k + 1 := by
  simp
  have h4 : k/2 ≤ k := by
    apply Nat.div_le_self
  have h5 : k < k + 1 := by
    simp
  apply Nat.lt_of_le_of_lt h4
  apply h5 
have h4 : k + 1 < k + 1 + 1 := by
  simp
simp[Nat.succ_eq_add_one] 
try apply h3
try apply h4


-- def inverse (a : ℕ) (b : ℕ)(h : (Nat.gcd a b) = 1) : ℕ :=

def inverse (a : ℕ) (b : ℕ): ℕ := 
  let (x, _) := Nat.xgcd a b
  if x < 0 then
    b - ((Int.natAbs x) % b)
  else
    (Int.natAbs x) % b


structure Public_key  where 
  n : ℕ 
  e : ℕ 
  hneq0 : n ≠ 0 
  deriving Repr
#check Public_key 
structure Key_pair extends Public_key where
  p : ℕ
  hp : Nat.Prime p
  q : ℕ 
  hq : Nat.Prime q
  ho : p ≠ q
  hn : n = p * q
  he : 2 < e ∧ Nat.gcd e (Nat.lcm (p - 1) (q - 1)) = 1
  deriving Repr

/- The key generation Function-/
def value_d(a : Key_pair) : ℕ   :=
  let d := inverse a.e (Nat.lcm (a.p - 1) (a.q - 1)) 
  d

structure Private_key extends Key_pair where
  d : ℕ
  hd : d = (value_d toKey_pair)
  deriving Repr

def key_generation  (a : Key_pair) : Private_key := 
  let d := (value_d a)
  have h : d = (value_d a) := rfl
  Private_key.mk a d h


/- The encryption Function-/
def encryption (a : Public_key) (m : ℕ) : ℕ := 
  mod_pow m a.e a.n 


/- The decryption Function-/
def decryption (b : Private_key)(me : ℕ) : ℕ := 
  mod_pow me b.d b.n 
