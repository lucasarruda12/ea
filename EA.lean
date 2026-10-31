import EA.Basic

-- Eu recomendo começar com um alt + z, para dar wrap nas linhas. Porque os comentários são muito longos :P

/- Considere uma operac¸˜ao bin´aria θ sobre N em que xθy = min(x, y). Esta operac¸˜ao
tem elemento neutro? E se considerar a operac¸˜ao θ′ em N em que tal operac¸˜ao ´e
dada por xθ′y = max(x − y, 0)? A operac¸˜ao θ′ ter´a elemento neutro?
-/

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

namespace ex2

/-
ado n ∈ N1, denote-se por An o conjunto {1, . . . , n}, e por Pn o conjunto das
permutac¸˜oes de An. Mostre que a operac¸˜ao ◦ (composic¸˜ao de func¸˜oes) em Pn
(a) ´e comutativa se n = 1 ou n = 2.
(b) n˜ao ´e comutativa se n ≥ 3.
-/

#check Fin 2 -- Todos os naturais menores que 2

structure Perm (n : Nat) where
  f : Fin n -> Fin n
  f_inv : Fin n -> Fin n
  f_inv_right : f ∘ f_inv = id
  f_inv_left : f_inv ∘ f = id

theorem one_comm : ∀ p q : Perm 1, p.f ∘ q.f = q.f ∘ p.f := by
  intro p q
  funext ⟨x, hx⟩
  have this : x = 0 := by
    exact Nat.lt_one_iff.mp hx
  simp [this]
  



end ex2
