import Lean.Data.Parsec
def main (args : List String) : IO Unit := do 
  let stdin ← IO.getStdin
  IO.println "Enter the message to be encrypted "
  let input ← stdin.getLine

  IO.println s!"The message is {input}"