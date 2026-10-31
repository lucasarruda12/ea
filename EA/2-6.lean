import EA.«1-10»

namespace ex6

variable {G : Type} [Group G]

def f (g x : G) : G := g * x * g⁻¹

theorem is_hom (g : G) : ∀ (x y : G), f g (x * y) = (f g x) * (f g y) := by
  intro x y
  rw [f, f, f]
  apply Eq.symm
  calc
    g * x * g⁻¹ * (g * y * g⁻¹)
      = g * x * (g⁻¹ * g) * y * g⁻¹
      := by simp [Group.mul_assoc]
    _ = g * x * 1 * y * g⁻¹
      := by rw [Group.inv_mul]
    _ = g * x * y * g⁻¹
      := by rw [Group.mul_one]
    _ = g * (x * y) * g⁻¹
      := by simp [Group.mul_assoc]

theorem is_inj (g : G) : ∀ (x y : G), f g x = f g y → x = y := by
  intro x y h
  rw [f, f] at h
  have h := congrArg (fun x => g⁻¹ * x * g) h
  rw [Group.mul_assoc g x (g⁻¹)] at h
  rw [← Group.mul_assoc (g⁻¹) g (x * g⁻¹)] at h
  rw [Group.inv_mul, Group.one_mul] at h
  rw [Group.mul_assoc] at h
  rw [Group.inv_mul, Group.mul_one] at h

  rw [Group.mul_assoc g y (g⁻¹)] at h
  rw [← Group.mul_assoc (g⁻¹) g (y * g⁻¹)] at h
  rw [Group.inv_mul, Group.one_mul] at h
  rw [Group.mul_assoc] at h
  rw [Group.inv_mul, Group.mul_one] at h
  exact h


theorem is_sur (g : G) : ∀ y : G, ∃ x : G, f g x = y := by
  intro y
  exists (g⁻¹ * y * g)
  rw [f]
  calc
    g * (g⁻¹ * y * g) * g⁻¹
      = (g * g⁻¹) * y * (g * g⁻¹)
    := by simp [Group.mul_assoc]
    _ = 1 * y * 1
    := by rw [Group.mul_inv]
    _ = y
      := by rw [Group.one_mul, Group.mul_one]


-- Quando o grupo é abeliano, a função f é sua própria inversa

variable (mul_com : ∀ g h : G, g * h = h * g)

include mul_com in
theorem self_inv (g : G) : f g ∘ f g = id := by
  funext x
  rw [Function.comp, f, f, id]
  rw [mul_com g x, Group.mul_assoc x g _]
  rw [Group.mul_inv, Group.mul_one]
  rw [mul_com]
  rw [← Group.mul_assoc]
  rw [Group.inv_mul, Group.one_mul]



end ex6
