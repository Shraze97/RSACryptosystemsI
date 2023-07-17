import Lean
open Lean Parsec

#check Parsec

#check Json.parse -- Copied from here


partial def natCore (acc : Nat := 0) : Parsec Nat := do
  let some c ← peek? | return acc
  if '0' ≤ c ∧ c ≤ '9' then
    skip
    let acc' := 10*acc + (c.val.toNat - '0'.val.toNat)
    natCore acc'
  else
    return acc

@[inline]
def lookahead (p : Char → Prop) (desc : String) [DecidablePred p] : Parsec Unit := do
  let c ← peek!
  if p c then
    return ()
  else
    fail <| "expected " ++ desc

@[inline]
def parseNat : Parsec Nat := do
  lookahead (fun c => '0' ≤ c ∧ c ≤ '9') "digit"
  natCore 0

partial def parseArrayCore (p : Parsec α) (acc : Array α := #[]) : Parsec (Array α) := do
  ws
  let a ← p
  let acc' := acc.push a
  let c ← anyChar
  if c = ']' then
    return acc'
  else if c = ',' then
    parseArrayCore p acc'
  else
    fail s!"Unexpected character {c} in input."

def parseArray (p : Parsec α) : Parsec (Array α) := do
  ws
  skipChar '#'
  skipChar '['
  ws
  let c ← peek!
  if c = ']' then
    return #[]
  else
    parseArrayCore p #[]

abbrev parseNatArray (s : String) : IO (Array Nat) := parseArray parseNat |>.run s |> IO.ofExcept

#eval parseNatArray "#[10, 7]"