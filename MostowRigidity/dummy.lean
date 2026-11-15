def myAdd : Nat → Nat → Nat
  | a, Nat.zero => a
  | a, Nat.succ b => Nat.succ (myAdd a b)

#eval myAdd 3 5