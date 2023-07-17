import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Int.GCD
import Mathlib.Tactic
import Init 
   
def mod_pow (a : ℕ)(b : ℕ)(n : ℕ)(hneq : n ≠ 0) : ℕ :=
  match b with 
  | 0 => 1
  | Nat.succ k => 
    if k % 2 = 1 then 
    let c := mod_pow a ((k + 1)/2) n hneq 
    (c * c) % n 
  else 
    (a * (mod_pow a k n hneq)) % n 
termination_by _ _ => b
decreasing_by      
simp
rw[← Nat.add_one k] 
have h1 : k < k + 1 := by
  simp
have h2 : (k + 1)/2 < k + 1 := by
  simp
  apply Nat.div_lt_self
  simp
  trivial
try apply h1
try apply h2 

def inverse (a : ℕ) (b : ℕ)(h : (Nat.gcd a b) = 1) : ℕ := 
  let (x, _) := Nat.xgcd a b
  if x < 0 then
    b - ((Int.natAbs x) % b)
  else
    (Int.natAbs x) % b

@[ext]
structure Public_key  where 
  n : ℕ 
  e : ℕ 
  hneq0 : n > 1  
  deriving Repr

theorem gt_1_neq_0 (a : ℕ )(ha : a > 1) : a ≠ 0 := by
  intro h
  linarith
  
structure Key_pair extends Public_key where
  p : ℕ
  hp : Nat.Prime p := by decide
  q : ℕ 
  hq : Nat.Prime q := by decide
  ho : p ≠ q := by decide
  hn : n = p * q := by rfl
  he : 2 < e ∧ Nat.gcd e (Nat.lcm (p - 1) (q - 1)) = 1 := by constructor<;> decide 
  deriving Repr

/- The key generation Function-/
def value_d (a : Key_pair) : ℕ :=
  let d := inverse a.e (Nat.lcm (a.p - 1) (a.q - 1)) a.he.right
  d

structure Private_key extends Key_pair where
  d : ℕ
  hd : d = (value_d toKey_pair)
  deriving Repr

def key_generation  (a : Key_pair) : Private_key := 
  let d := (value_d a)
  have h : d = (value_d a) := rfl
  Private_key.mk a d h


def Private_key_gen (p : ℕ)(q : ℕ)(hp : Nat.Prime p)(hq : Nat.Prime q)(ho : p ≠ q)(e : ℕ )(he1 : Nat.coprime e (Nat.lcm (p - 1) (q - 1)))(he2 : 2 < e) : Private_key := 
  let n := p * q
  let he : 2 < e ∧ Nat.gcd e (Nat.lcm (p - 1) (q - 1)) = 1 := by 
    constructor
    exact he2
    exact he1
  have hn : n = p * q := by rfl
  have hneq0 : n > 1 := by 
    rw[hn]
    have h1 : 1 = 1 * 1 := by rfl
    rw[h1]
    apply Nat.mul_lt_mul
    exact hp.one_lt
    exact LT.lt.le hq.one_lt
    simp
  let a := Public_key.mk n e hneq0
  let b := Key_pair.mk a p hp q hq ho hn he 
  key_generation b
  


/- The encryption Function-/
def encryption (a : Public_key) (m : ℕ) : ℕ := 
  mod_pow m a.e a.n (gt_1_neq_0 a.n (a.hneq0)) 


/- The decryption Function-/
def decryption (b : Private_key)(me : ℕ) : ℕ := 
  mod_pow me b.d b.n (gt_1_neq_0 b.n (b.hneq0))
