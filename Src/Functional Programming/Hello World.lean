partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.getLine
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write ("get: " ++ buf).toUTF8
    dump stream

def sleepThenTick (ms : UInt32) : IO Unit := do
  let mut i := 0
  while true do
    IO.sleep ms
    IO.println s!"tick {i}"
    i := i + 1


def main : IO Unit := do
  sleepThenTick 1000
