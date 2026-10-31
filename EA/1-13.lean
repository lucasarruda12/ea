import EA.«1-10»

namespace ex13

def Set (T : Type) := T → Prop
def Set.mem (A : Set T) (t : T) := A t

instance : Membership T (Set T) where
    mem := Set.mem

axiom A : Type
variable [Group A]
axiom B : Set A
axiom B_hab : ∃ b : A, b ∈ B
axiom B_div_fechado : ∀ x y : A, x ∈ B → y ∈ B → x*y⁻¹ ∈ B

theorem one : 1 ∈ B := by
    have ⟨b, hb⟩ := B_hab
    have := B_div_fechado b b hb hb
    rw [Group.mul_inv] at this
    assumption

theorem inv : ∀ b ∈ B, b⁻¹ ∈ B := by
    intro b hb
    have := B_div_fechado 1 b one hb
    rw [Group.one_mul] at this
    assumption

theorem mul : ∀ x y : A, x ∈ B → y ∈ B → x*y ∈ B := by
    intro x y hx hy
    have := B_div_fechado x (y⁻¹) hx (inv y hy)
    rw [ex10.inv_inv] at this
    assumption

end ex13
