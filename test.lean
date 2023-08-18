example (n : Nat) (hn : n-1 = 1) : n = 2 := by
  refine Nat.eq_add_of_sub_eq (?_) hn
  cases n 
  · simp at hn
  · apply Nat.succ_le_succ (Nat.zero_le _)



theorem a (_h : n - 1 = 1) :
   n = 2 :=
   match n with
   | 2 => rfl


#print a