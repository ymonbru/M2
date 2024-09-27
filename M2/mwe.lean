
def step (n:Nat): Bool × Nat:= match n with
  |0 => (true,0)
  |n + 1 => (false, n)

def exemple (n:Nat): Nat :=
  let res:= step n
  if res.1 then
    n
  else
    have : res.2 < n:= by
      sorry
    exemple res.2
