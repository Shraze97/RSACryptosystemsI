-- import «RSACryptosystemsI»
-- import RSACryptosystemsI.MainStructure

def main (args : List String) : IO Unit := do 
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  IO.print "Enter the message to be encrypted "

#eval main []