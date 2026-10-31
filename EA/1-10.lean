class Group (G : Type) : Type
  extends
    Mul G, One G, Inv G
where
  mul_assoc (a b c : G) : a * b * c = a * (b * c)
  one_mul (a : G) : 1 * a = a
  mul_one (a : G) : a * 1 = a
  mul_inv (a : G) : a * a⁻¹ = 1
  inv_mul (a : G) : a⁻¹ * a = 1

namespace ex10

variable (G : Type) [Group G]

theorem invol (a : G) : a * a = a → a = 1 := by
  intro a_a
  have this : (a * a) * a⁻¹ = a * a⁻¹ := by
    exact congrArg (fun x => x * a⁻¹) a_a
  rw [Group.mul_assoc, Group.mul_inv] at this
  rw [Group.mul_one] at this
  assumption

theorem left_cancel (a b c : G)
  : a * b = a * c → b = c
:= by
  intro h
  have this : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by
    exact congrArg (fun x => a⁻¹ * x) h
  rw [← Group.mul_assoc, ← Group.mul_assoc] at this
  rw [Group.inv_mul] at this
  rw [Group.one_mul, Group.one_mul] at this
  assumption

theorem right_cancel (a b c : G)
  : b * a = c * a → b = c
:= by
  intro h
  have this : (b * a) * a⁻¹ = (c * a) * a⁻¹ := by
    exact congrArg (fun x => x * a⁻¹) h
  rw [Group.mul_assoc, Group.mul_assoc] at this
  rw [Group.mul_inv] at this
  rw [Group.mul_one, Group.mul_one] at this
  assumption

theorem inv_inv (a : G) : (a ⁻¹) ⁻¹ = a := by
  rw [← Group.mul_one (a⁻¹)⁻¹]
  rw [← Group.inv_mul a]
  rw [← Group.mul_assoc]
  rw [Group.inv_mul, Group.one_mul]

theorem res_unic_left (a b : G)
  : ∀x, x * a = b → x = b * a⁻¹
:= by
  intro x hx
  have this : x * a * a⁻¹ = b * a⁻¹ := by
    exact congrArg (fun y => y * a⁻¹) hx
  rw [Group.mul_assoc] at this
  rw [Group.mul_inv] at this
  rw [Group.mul_one] at this
  assumption

theorem res_unic_right (a b : G)
  : ∀y,  a * y = b → y = a⁻¹ * b
:= by
  intro y hy
  have this : a⁻¹ * (a * y) = a⁻¹ * b := by
    exact congrArg (fun y => a⁻¹ * y) hy
  rw [← Group.mul_assoc] at this
  rw [Group.inv_mul] at this
  rw [Group.one_mul] at this
  assumption

theorem inv_prod (a b : G) :
  (a * b)⁻¹ = b⁻¹ * a⁻¹
:= by
  have h : (a * b) * (a * b)⁻¹ = 1 := by
    exact Group.mul_inv (a * b)
  have h2 : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    rw [Group.mul_assoc]
    rw [← Group.mul_assoc b]
    rw [Group.mul_inv, Group.one_mul]
    rw [Group.mul_inv]
  have h2 :=
    res_unic_right G (a * b) 1 (b⁻¹ * a⁻¹) h2
  rw [Group.mul_one] at h2
  rw [h2]

end ex10
