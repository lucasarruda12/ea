import EA.«2-7»

class Field (F : Type) extends
  Ring F, Inv F
where
  one_neq_zero : 1 ≠ 0
  mul_inv_ne_zero : ∀ x : F, x ≠ 0 → x * x⁻¹ = 1
  inv_mul_ne_zero : ∀ x : F, x ≠ 0 → x⁻¹ * x = 1
