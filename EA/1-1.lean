namespace ex1

infixl:65 " θ " => Nat.min
#check 3 θ 2 -- Pode passar o mouse aqui!
#eval 3 θ 2

theorem exists_theta_id : ¬∃x : Nat, ∀ n : Nat, x θ n = n := by
  intro h
  have ⟨m, hm⟩ := h
  have this := hm (m + 1)
  simp at this

infixl:65 " θ' " => Nat.max
#check 3 θ' 2 -- Pode passar o mouse aqui!
#eval 3 θ' 2

theorem exists_thetap_id : ∃x : Nat, ∀n : Nat, x θ' n = n := by
  exists 0
  intro n
  simp

end ex1
